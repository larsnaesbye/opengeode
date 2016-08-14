#!/usr/bin/env python
# -*- coding: utf-8 -*-

# pylint: disable=C0302
"""
    OpenGEODE - A tiny, free SDL Editor for TASTE

    SDL is the Specification and Description Language (Z100 standard from ITU)

    Copyright (c) 2012-2013 European Space Agency

    Designed and implemented by Maxime Perrotin

    Contact: maxime.perrotin@esa.int
"""

import signal
import sys
import os
import argparse
import logging
import traceback
import re
import code
import pprint
import random
from functools import partial
from itertools import chain

# pylint: disable=W0611
import undoCommands
import genericSymbols
import ogParser
import ogAST
import Renderer
import Clipboard
import Statechart
import Pr

# Enable mypy type checking
try:
    from typing import List, Union, Dict, Set, Any, Tuple
except ImportError:
    pass

try:
    import stringtemplate3  # NOQA
except ImportError:
    pass


from PySide import QtGui, QtCore
from PySide.QtCore import Qt, QSize, QFile, QIODevice, QRectF, QTimer, QPoint

from PySide.QtUiTools import QUiLoader
from PySide import QtSvg

from genericSymbols import(Symbol, Comment, Cornergrabber, Connection)
from sdlSymbols import(Input, Output, Decision, DecisionAnswer, Task,
        ProcedureCall, TextSymbol, State, Start, Join, Label, Procedure,
        ProcedureStart, ProcedureStop, StateStart, Connect, Process,
        ContinuousSignal)
from TextInteraction import EditableText

# Icons and png files generated from the resource file:
import icons  # NOQA

# Logging: ist of properly loaded modules that will use it
LOG = logging.getLogger(__name__)

__all__ = ['Scene']


# Global handling all top-level elements
# It seems that if we don't keep a global list of these elements
# (START, STATE, and Text symbols)
# they sometimes get destroyed and disappear from the scene.
# As if a GC was deleting these object *even if they belong to the scene*
# (but have no parentItem). Most likely a Qt/Pyside bug.
G_SYMBOLS = set()

# Other Qt bug:
# QGraphicsTextItem don't stand that their parent item (usually an
# SDL symbol) is removed from the scene (scene.removeItem()). It
# provokes segfault when application exits.
# Workaround is to use hide()/show() to make items disappear
# from the scene (when deleted). Seems OK (MP 2013-03-26)

# Lookup table used to configure the context-dependent toolbars
ACTIONS = {
    'block': [Process, Comment, TextSymbol],
    'process': [Start, State, Input, Connect, ContinuousSignal, Task, Decision,
                DecisionAnswer, Output, ProcedureCall, TextSymbol, Comment,
                Label, Join, Procedure],
    'procedure': [ProcedureStart, Task, Decision,
                  DecisionAnswer, Output, ProcedureCall, TextSymbol,
                  Comment, Label, Join, ProcedureStop],
    'statechart': [],
    'state': [StateStart, State, Input, Connect, ContinuousSignal, Task,
              Decision, DecisionAnswer, Output, ProcedureCall, TextSymbol,
              Comment, Label, Join, ProcedureStop, Procedure],
    'clipboard': [Start, State, Input, Connect, Task, Decision, DecisionAnswer,
                  Output, ProcedureCall, TextSymbol, Comment, Label,
                  Join, Procedure, Process, StateStart, ProcedureStop,
                  ContinuousSignal],
    'lander': [],
    'asn1': []
}



class Scene(QtGui.QGraphicsScene, object):
    ''' Main graphic scene (canvas) where the user can place symbols '''
    # Signal to be emitted when the scene is left (e.g. UP button)
    scene_left = QtCore.Signal()

    def __init__(self, context='process'):
        '''
            Create an SDL Scene for a given context:
            process, procedure or composite state
        '''
        super(Scene, self).__init__()
        # Reference to the parent scene
        self.parent_scene = None
        self.mode = 'idle'
        self.context = context
        self.allowed_symbols = ACTIONS[context]
        # Configure the action menu
        all_possible_actions = set()
        for action in ACTIONS.viewvalues():
            all_possible_actions |= set(action)
        self.actions = {action.__name__: partial(self.add_symbol, action)
                for action in all_possible_actions}

        # Create a stack for handling undo/redo commands
        # (defined in undoCommands.py)
        self.undo_stack = QtGui.QUndoStack(self)
        # buttonSelected is used to set which symbol to draw
        # on next scene click (see mousePressEvent)
        self.button_selected = None
        self.setBackgroundBrush(QtGui.QBrush(
                                           QtGui.QImage(':icons/texture.png')))
        self.messages_window = None
        self.click_coordinates = None
        self.orig_pos = None
        self.process_name = 'opengeode'
        # Scene name is used to update the tab window name when scene changes
        self.name = ''
        # search_item/search_pattern are used for search/replace function
        self.search_item = None
        self.search_pattern = None
        # Selection rectangle when user clicks on the scene and moves mouse
        self.select_rect = None
        # Keep a list of composite states: {'stateName': Scene}
        self._composite_states = {}
        # Keep a track of highlighted symbols: { symbol: brush }
        self.highlighted = {}
        self.refresh_requested = False


    def is_aggregation(self):
        ''' Determine if the current scene is a state aggregation, i.e. if
        if contains only floating states without children
        '''
        for each in self.visible_symb:
            if each.hasParent:
                return False
            if not isinstance(each, State):
                # At the moment do not support Text Areas
                return False
            if any(child for child in each.childSymbols()
                    if isinstance(child, (Input, ContinuousSignal))):
                return False
        return True


    @property
    def visible_symb(self):
        ''' Return the visible items of a scene '''
        return (it for it in self.items() if it.isVisible() and
                isinstance(it, Symbol))


    @property
    def editable_texts(self):
        ''' Return all EditableText areas of a scene '''
        return (it for it in self.items() if it.isVisible() and
                isinstance(it, EditableText))


    @property
    def floating_symb(self):
        ''' Return the top level floating items of a scene '''
        return (it for it in self.visible_symb if not it.hasParent)


    @property
    def processes(self):
        ''' Return visible processes components of the scene '''
        return (it for it in self.visible_symb if isinstance(it, Process) and
                not isinstance(it, Procedure))


    @property
    def procedures(self):
        ''' Return visible procedures components of the scene '''
        return (it for it in self.visible_symb if isinstance(it, Procedure))


    @property
    def states(self):
        ''' Return visible state components of the scene '''
        return (it for it in self.visible_symb if isinstance(it, State))


    @property
    def texts(self):
        ''' Return visible text areas components of the scene '''
        return (it for it in self.visible_symb if isinstance(it, TextSymbol))


    @property
    def procs(self):
        ''' Return visible procedure declaration components of the scene '''
        return (it for it in self.visible_symb if isinstance(it, Procedure))


    @property
    def start(self):
        ''' Return visible start components of the scene '''
        return (it for it in self.visible_symb if isinstance(it, Start))


    @property
    def floating_labels(self):
        ''' Return visible floating label components of the scene '''
        return (it for it in self.floating_symb if isinstance(it, Label))


    @property
    def returns(self):
        ''' Return visible return components of the scene '''
        return (it for it in self.visible_symb if isinstance(it,
                                                              ProcedureStop))


    @property
    def composite_states(self):
        ''' Return states that contain a composite part '''
        # Update the list first
        for each in self.states:
            if each.is_composite() and \
                  each.nested_scene not in self._composite_states.viewvalues():
                self._composite_states[unicode(each).split()[0].lower()] = \
                                                            each.nested_scene
        return self._composite_states


    @composite_states.setter
    def composite_states(self, value):
        ''' Attribute setter '''
        self._composite_states = value


    @property
    def all_nested_scenes(self):
        ''' Return all nested scenes, recursively '''
        for each in self.visible_symb:
            if each.nested_scene and isinstance(each.nested_scene, Scene):
                yield each.nested_scene
                for sub in each.nested_scene.all_nested_scenes:
                    yield sub


    @property
    def path(self):
        ''' Get the path to the current scene as a list
        e.g. ['BLOCK a', 'PROCESS b', ...]
        '''
        if not self.parent_scene:
            return [self.name[0:-3]]
        return self.parent_scene.path + [self.name[0:-3]]


    @property
    def selected_symbols(self):
        ''' Generate the list of selected symbols (excluding grabbers) '''
        for selection in self.selectedItems():
            if isinstance(selection, Symbol):
                yield selection
            elif isinstance(selection, Cornergrabber):
                yield selection.parent


    def quit_scene(self):
        ''' Called in case of scene switch (e.g. UP button) '''
        pass


    def render_everything(self, ast):
        ''' Render a process and its children scenes, recursively '''
        already_created = []

        def recursive_render(content, dest_scene):
            ''' Process the rendering in scenes and nested scenes '''
            if isinstance(content, ogAST.Process):
                # XXX - should be set when entering the process
                self.process_name = ast.processName

            try:
                # Render top-level items and their children:
                for each in Renderer.render(content, dest_scene):
                    G_SYMBOLS.add(each)
                # Refreshing the scene may result in resizing some symbols
                dest_scene.refresh()
                # Once everything is rendered, adjust position of each
                # symbol to the value from the AST (positions may be
                # slightly altered by the reshaping functions)
                def fix_pos_from_ast(symbol):
                    try:
                        if symbol.ast.pos_x and symbol.ast.pos_y:
                            relpos = symbol.mapFromScene(symbol.ast.pos_x,
                                                         symbol.ast.pos_y)
                            #symbol.pos_x += relpos.x()
                            #symbol.pos_y += relpos.y()
                            if not symbol.hasParent:
                                symbol.pos_x = symbol.ast.pos_x
                                symbol.pos_y = symbol.ast.pos_y
                            else:
                                symbol.position += relpos
                            symbol.update_connections()
                            # Update_position is called here because it
                            # is not possible to be sure that the
                            # positionning stored in the file will be
                            # rendered correctly on the host plaform.
                            # Font rendering may cause slight differences
                            # between Linux and Windows for example.
                            symbol.update_position()
                        else:
                            # No CIF coordinates: fix COMMENT position
                            if isinstance(symbol, genericSymbols.Comment):
                                symbol.pos_x = \
                                  symbol.parent.boundingRect().width() + 15
                                symbol.pos_y = 0
                            if not symbol.hasParent:
                                sc_br = dest_scene.itemsBoundingRect()
                                sy_br = symbol.mapRectToScene(
                                            symbol.boundingRect() |
                                            symbol.childrenBoundingRect())
                                symbol.pos_x += (sc_br.width() - sy_br.x())
                    except AttributeError:
                        # no AST, ignore (e.g. Connections, Cornergrabbers)
                        pass
                    else:
                        # Recursively fix pos of sub branches and followers
                        for branch in (elm for elm in symbol.childSymbols()
                                   if isinstance(elm,
                                         genericSymbols.HorizontalSymbol)):
                            fix_pos_from_ast(branch)
                        fix_pos_from_ast(symbol.next_aligned_symbol())
                        fix_pos_from_ast(symbol.comment)
                map(fix_pos_from_ast, dest_scene.floating_symb)
            except TypeError:
                LOG.error(traceback.format_exc())

            # Render nested scenes, recursively:
            for each in (item for item in dest_scene.visible_symb
                         if item.nested_scene):
                LOG.debug(u'Recursive scene: ' + unicode(each))
                if isinstance(each.nested_scene, ogAST.CompositeState) \
                        and (not each.nested_scene.statename
                             or each.nested_scene in already_created):
                    # Ignore nested state scenes that already exist
                    LOG.debug('Subscene "{}" ignored'.format(unicode(each)))
                    continue
                subscene = \
                        self.create_subscene(each.__class__.__name__.lower(),
                                             dest_scene)
                already_created.append(each.nested_scene)
                subscene.name = unicode(each)
                LOG.debug('Created scene: {}'.format(subscene.name))
                recursive_render(each.nested_scene.content, subscene)
                each.nested_scene = subscene

            # Make sure all composite states are initially up to date
            # (Needed for the symbol shape to have dashed lines)
            for each in dest_scene.states:
                if unicode(each).lower() in \
                        dest_scene.composite_states.viewkeys():
                    each.nested_scene = dest_scene.composite_states[
                                                         unicode(each).lower()]

        recursive_render(ast, self)


    def refresh(self):
        ''' Scene refresh - make sure it happens only once per cycle '''
        #LOG.debug('scene refresh requested by '
        #          + str(traceback.extract_stack(limit=2)[-2][1:3]))
        if not self.refresh_requested:
            self.refresh_requested = True
            QTimer.singleShot(0, self.scene_refresh)

    def scene_refresh(self):
        ''' Refresh the symbols and connections in the scene '''
        self.refresh_requested = False
        #LOG.debug('scene refresh done')
#       for symbol in self.visible_symb:
#           symbol.updateConnectionPointPosition()
#           symbol.updateConnectionPoints()
        for symbol in self.editable_texts:
            # EditableText refreshing - design explanation:
            # The first one is tricky: at symbol initialization,
            # the bounding rect of the text is computed from the raw
            # text value, without any formatting. However, it can
            # happen that text (especially when a model is loaded)
            # contains highlighted data (bold), which has the effect
            # of making the width of the text in fact wider than
            # the bounding rect. The set_text_alignment function,
            # that is applying the aligment of the text within its
            # bounding rect, can work only if the text width is fixed.
            # It has to set it according to the bounding rect, which,
            # therefore can be too small, and this has the effect of
            # pushing the exceeding character to the next line.
            # The only way to avoid this is to call setTextWidth
            # with the value -1 before the aligment is computed.
            # This has the effect of re-computing the bounding rect
            # and fixing the width issue.
            symbol.setTextWidth(-1)
            #symbol.set_textbox_position()
            symbol.try_resize()
            symbol.set_text_alignment()
        for symbol in self.visible_symb:
            symbol.update_connections()


    def set_cursor(self, follower):
        ''' Set the cursor shape depending on the selected menu item '''
        for item in self.items():
            try:
                if follower.__name__ not in item.allowed_followers:
                    item.setCursor(Qt.ForbiddenCursor)
                else:
                    item.setCursor(Qt.PointingHandCursor)
            except AttributeError:
                # if there are items not having allowed_followers
                pass


    def reset_cursor(self):
        ''' Reset the default cursor of an item '''
        for item in self.items():
            try:
                item.setCursor(item.default_cursor)
            except AttributeError:
                pass


    def translate_to_origin(self):
        '''
            Translate all items to coordinate system starting at (0,0),
            in order to avoid negative coordinates
        '''
        try:
            min_x = min(item.x() for item in self.visible_symb)
            min_y = min(item.y() for item in self.visible_symb)
        except ValueError:
            # No item in the scene
            return 0, 0
        delta_x = -min_x if min_x < 0 else 0
        delta_y = -min_y if min_y < 0 else 0
        for item in self.floating_symb:
            item.pos_x += delta_x
            item.pos_y += delta_y
        return delta_x, delta_y


    def set_selection(self, toolbar):
        ''' When the selection has changed, update menu, etc '''
        toolbar.update_menu(self)
        for item in self.selected_symbols:
            item.grabber.display()


    def syntax_errors(self, symb):
        ''' Parse a symbol and return a list of syntax errors '''
        return symb.check_syntax('\n'.join(Pr.generate(symb, recursive=False)))


    def check_syntax(self, symbol):
        ''' Check syntax of a symbol and display a pop-up in case of errors '''
        errors = self.syntax_errors(symbol)

        if not errors:
            return

        for view in self.views():
            errs = []
            for error in errors:
                split = error.split()
                if split[0] == 'line' and len(split) > 1:
                    line_col = split[1].split(':')
                    if len(line_col) == 2:
                        # Get line number and column..to locate error
                        # line_nb, col = line_col
                        errs.append(' '.join(split[2:]))
                    else:
                        errs.append(error)
                else:
                    errs.append(error)
            self.clear_focus()
            msg_box = QtGui.QMessageBox(view)
            msg_box.setIcon(QtGui.QMessageBox.Warning)
            msg_box.setWindowTitle('OpenGEODE - Syntax Error')
            msg_box.setInformativeText('\n'.join(errs))
            msg_box.setText("Syntax error!")
            msg_box.setStandardButtons(QtGui.QMessageBox.Discard)
            msg_box.setDefaultButton(QtGui.QMessageBox.Discard)
            msg_box.exec_()


    def global_syntax_check(self, ignore=set()):
        ''' Parse each visible symbol in the current scene and its children
            and check syntax using the parser
            Use a mutable parameter to avoid recursion on already visited
            scenes
        '''
        res = True
        reset = not ignore
        ignore.add(self)
        for each in self.visible_symb:
            errors = self.syntax_errors(each)
            if errors:
                res = False
            for err in errors:
                split = err.split()
                if split[0] == 'line' and len(split) > 1:
                    line_col = split[1].split(':')
                    if len(line_col) == 2:
                        # get line and col. line must be decremented because
                        # line 1 is the CIF comment which is not visible
                        line_nb, col = line_col
                        line_nb = int(line_nb) - 1
                        split[1] = '{}:{}'.format(line_nb, col)
                pos = each.scenePos()
                fmt = [[' '.join(split), [pos.x(), pos.y()], self.path]]
                log_errors(self.messages_window, fmt, [], clearfirst=False)

        for each in self.all_nested_scenes:
            if each not in ignore:
                if not each.global_syntax_check():
                    res = False
        if reset:
            ignore.clear()
        return res


    def update_completion_list(self, symbol):
        ''' When text has changed on a symbol, update the data dictionnary '''
        pr_text = '\n'.join(Pr.generate(symbol,
                                        recursive=False,
                                        nextstate=False, cpy=True))
        symbol.update_completion_list(pr_text=pr_text)


    def highlight(self, item):
        ''' Highlight a symbol '''
        if item in self.highlighted:
            return
        bound = item.boundingRect()
        center = bound.center().x()
        gradient = QtGui.QLinearGradient(center, 0, center, bound.height())
        gradient.setColorAt(0, Qt.cyan)
        gradient.setColorAt(1, Qt.white)
        self.highlighted[item] = item.brush()
        item.setBrush(QtGui.QBrush(gradient))

    def clear_highlight(self, item=None, reset=True):
        ''' Remove the highlighting of one item or all items on the scene '''
        if item in self.highlighted:
            self.setBrush(self.highlighted.pop(item))
        if reset:
            for item, brush in self.highlighted.viewitems():
                item.setBrush(brush)
            self.highlighted = {}


    def find_text(self, pattern):
        ''' Return all symbols with matching text '''
        for item in (symbol for symbol in self.items()
                     if isinstance(symbol, EditableText)
                     and symbol.isVisible()):
            try:
                res = re.search(pattern, unicode(item), flags=re.IGNORECASE)
            except re.error:
                # invalid pattern
                raise StopIteration
            if res:
                yield item.parentItem()


    def search(self, pattern, replace_with=None):
        ''' Search and replace function ; get next search result with key n '''
        self.clearSelection()
        self.clear_highlight()
        self.clear_focus()
        if pattern.endswith('\\'):
            # Avoid buggy pattern ending with a single backslash
            pattern += '\\'
        self.search_item = self.find_text(pattern)
        self.search_pattern = pattern
        if replace_with:
            with undoCommands.UndoMacro(self.undo_stack, 'Search and Replace'):
                for item in self.search_item:
                    new_string = re.sub(pattern,
                                        replace_with,
                                        unicode(item.text),
                                        flags=re.IGNORECASE)
                    undo_cmd = undoCommands.ReplaceText(
                                     item.text, unicode(item.text), new_string)
                    self.undo_stack.push(undo_cmd)
                    item.select()
            self.refresh()
        else:
            try:
                item = self.search_item.next()
                item.select()
                self.highlight(item)
                item.ensureVisible()
            except StopIteration:
                LOG.info('Pattern not found')


    def delete_selected_symbols(self):
        '''
            Remove selected symbols from the scene, with proper re-connections
        '''
        self.undo_stack.beginMacro('Delete items')
        for item in self.selected_symbols:
            if not item.scene():
                # Ignore if item has already been deleted
                # (in case of multiple selection)
                continue
            undo_cmd = undoCommands.DeleteSymbol(item)
            self.undo_stack.push(undo_cmd)
            try:
                item.branchEntryPoint.parent.updateConnectionPointPosition()
                item.branchEntryPoint.parent.updateConnectionPoints()
            except AttributeError:
                pass
        self.undo_stack.endMacro()


    def copy_selected_symbols(self):
        '''
            Create a copy of selected symbols to a buffer (in AST form)
            Called when user presses Ctrl-C
        '''
        self.click_coordinates = None
        try:
            Clipboard.copy(self.selected_symbols)
        except TypeError as error_msg:
            try:
                self.messages_window.addItem(unicode(error_msg))
            except AttributeError:
                LOG.error(unicode(error_msg))
            raise


    def cut_selected_symbols(self):
        '''
            Create a copy of selected symbols, then delete them
        '''
        try:
            self.copy_selected_symbols()
        except TypeError:
            LOG.error('Copy error - Cannot cut')
        else:
            self.delete_selected_symbols()


    def paste_symbols(self):
        '''
            Paste previously copied symbols at selection point
        '''
        parent = list(self.selected_symbols)
        if len(parent) > 1:
            self.messages_window.addItem(
                    'Cannot paste when several items are selected')
        else:
            parent_item, = parent or [None]
            try:
                new_items = Clipboard.paste(parent_item, self)
            except TypeError as error_msg:
                LOG.error(str(error_msg))
                try:
                    self.messages_window.addItem(str(error_msg))
                except AttributeError:
                    pass
            else:
                self.undo_stack.beginMacro('Paste')
                for item in new_items:
                    # Allow pasting inputs when input is selected
                    # Same for decision answers and connections
                    if(isinstance(parent_item, genericSymbols.HorizontalSymbol)
                            and type(parent_item) == type(item)):
                        parent_item = parent_item.parentItem()

                    undo_cmd = undoCommands.InsertSymbol(item, parent_item,
                            pos=None if parent_item
                                     else self.click_coordinates or item.pos())

                    self.undo_stack.push(undo_cmd)
                    if parent_item:
                        parent_item = item
                    else:
                        G_SYMBOLS.add(item)
                    item.cam(item.pos(), item.pos())
                self.undo_stack.endMacro()
                self.refresh()


    def sdl_to_statechart(self, basic=True):
        ''' Create a graphviz representation of the SDL model '''
        pr_raw = Pr.parse_scene(self)
        pr_data = unicode('\n'.join(pr_raw))
        ast, _, _ = ogParser.parse_pr(string=pr_data)
        try:
            process_ast, = ast.processes
        except ValueError:
            LOG.debug('No statechart to render')
            return None
        # Flatten nested states (no, because neato does not support it,
        # dot supports only vertically-aligned states, and fdp does not
        # support curved edges and is buggy with pygraphviz anyway)
        # Helper.flatten(process_ast)
        return Statechart.create_dot_graph(process_ast, basic)


    def export_branch_to_picture(self, symbol, filename, doc_format):
        ''' Save a symbol and its followers to a file '''
        temp_scene = Scene(context=self.context)
        temp_scene.messages_window = self.messages_window
        self.clearSelection()
        self.clear_highlight()
        symbol.select()
        try:
            self.copy_selected_symbols()
            temp_scene.paste_symbols()
            temp_scene.export_img(filename, doc_format)
        except AttributeError:
            pass


    def export_img(self, filename=None, doc_format='png', split=False):
        ''' Save the scene as a PNG/SVG or PDF document
            If specified, split the diagram in multiple files, one
            per top-level floating item
        '''
        if not filename:
            return

        if split:
            # Save in multiple files
            index = 0
            for item in self.floating_symb:
                name = '{}-{}'.format(filename, str(index))
                LOG.info('Saving {ext} file: {name}.{ext}'
                         .format(ext=doc_format, name=name))
                self.export_branch_to_picture(item, name, doc_format)
                index += 1

        if filename.split('.')[-1] != doc_format:
            filename += '.' + doc_format

        self.clearSelection()
        self.clear_highlight()
        self.clear_focus()
        # Copy in a different scene to get the smallest rectangle
        other_scene = Scene(context=self.context)
        other_scene.messages_window = self.messages_window
        other_scene.setBackgroundBrush(QtGui.QBrush())
        for each in self.floating_symb:
            each.select()
            try:
                self.copy_selected_symbols()
            except AttributeError as err:
                LOG.debug(str(traceback.format_exc()))
                LOG.error(str(err))
            other_scene.paste_symbols()
            each.select(False)
        rect = other_scene.sceneRect()

        # enlarge the rect to fit extra pixels due to antialiasing
        rect.adjust(-5, -5, 5, 5)
        if doc_format == 'png':
            device = QtGui.QImage(rect.size().toSize(),
                                  QtGui.QImage.Format_ARGB32)
            device.fill(Qt.transparent)
        elif doc_format == 'svg':
            device = QtSvg.QSvgGenerator()
            device.setFileName(filename)
            device.setTitle('OpenGEODE SDL Diagram')
            device.setSize(rect.size().toSize())
        elif doc_format == 'pdf':
            device = QtGui.QPrinter()
            device.setOutputFormat(QtGui.QPrinter.PdfFormat)
            device.setPaperSize(
                    rect.size().toSize(), QtGui.QPrinter.Point)
            device.setFullPage(True)
            device.setOutputFileName(filename)
        else:
            LOG.error('Output format not supported: ' + doc_format)
        painter = QtGui.QPainter(device)
        other_scene.render(painter, source=rect)
        try:
            device.save(filename)
        except AttributeError:
            # Due to inconsistencies in Qt API - only QtGui.QImage has the save
            pass
        if painter.isActive():
            painter.end()


    def clear_focus(self):
        ''' Clear focus from any item on the scene '''
        try:
            self.focusItem().clearFocus()
        except AttributeError:
            # if no focus item
            pass


    def symbol_near(self, pos, dist=5, selectable_only=True):
        ''' If any, returns symbol around pos '''
        items = self.items(
                QRectF(pos.x() - dist, pos.y() - dist, 2 * dist, 2 * dist))
        for item in items:
            if((selectable_only and item.flags() &
                    QtGui.QGraphicsItem.ItemIsSelectable)
                    or not selectable_only):
                return item.parent if isinstance(item, Cornergrabber) else item


    def can_insert(self, pos, item_type):
        ''' Check if we can add an item type at a given position '''
        parent_item = self.symbol_near(pos)
        if not parent_item:
            # No symbol at the given position
            if item_type.needs_parent:
                raise TypeError(str(item_type.__name__) + ' needs a parent')
            else:
                return None
        else:
            # Check if item as pos accepts item type as follower
            if item_type.__name__ in parent_item.allowed_followers:
                return parent_item
            else:
                raise TypeError(parent_item.__class__.__name__ +
                                ' symbol cannot be followed by ' +
                                item_type.__name__)


    def create_subscene(self, context, parent=None):
        ''' Create a new SDL scene, e.g. for nested symbols '''
        subscene = Scene(context=context)
        subscene.messages_window = self.messages_window
        subscene.parent_scene = parent
        return subscene


    def place_symbol(self, item_type, parent, pos=None):
        ''' Draw a symbol on the scene '''
        item = item_type()
        # Add the item to the scene
        if item not in self.items():
            self.addItem(item)
        # Create Undo command (makes the call to the insert_symbol function):
        undo_cmd = undoCommands.InsertSymbol(item=item, parent=parent, pos=pos)
        self.undo_stack.push(undo_cmd)
        # If no item is selected (e.g. new STATE), add it to the scene
        if not parent:
            G_SYMBOLS.add(item)

        if item_type == Decision:
            # When creating a new decision, add two default answers
            self.place_symbol(item_type=DecisionAnswer, parent=item)
            self.place_symbol(item_type=DecisionAnswer, parent=item)
        elif item_type in (Procedure, State, Process):
            # Create a sub-scene for clickable symbols
            item.nested_scene = \
                    self.create_subscene(item_type.__name__.lower(), self)

        self.clearSelection()
        self.clear_highlight()
        self.clear_focus()
        item.select()
        item.cam(item.pos(), item.pos())
        # When item is placed, immediately set focus to input text
        item.edit_text()

        for view in self.views():
            view.view_refresh()
            view.ensureVisible(item)
        return item



    def add_symbol(self, item_type):
        ''' Add a symbol, or postpone until a parent symbol is selected  '''
        try:
            # If an item is selected or if its text has focus,
            # use it as parent item for the newly inserted item
            selection, = (list(self.selected_symbols) or
                          [self.focusItem().parentItem()])
            with undoCommands.UndoMacro(self.undo_stack, 'Place Symbol'):
                self.place_symbol(item_type=item_type, parent=selection)
        except (ValueError, AttributeError):
            # Menu item clicked but no symbol selected
            # -> store until user clicks on the scene
            self.messages_window.clear()
            self.messages_window.addItem(
                    'Click on the scene to place the symbol')
            self.button_selected = item_type
            if item_type == Connection:
                self.mode = 'wait_connection_source'
            else:
                self.mode = 'wait_placement'
            self.set_cursor(item_type)
            return None



    # pylint: disable=C0103
    def mousePressEvent(self, event):
        '''
            Handle mouse click on the scene:
            If a symbol was selected in the menu, check if it can be inserted
            Otherwise store the coordinates, in which case if the user does
            a paste action with floating items, they will be placed there.
        '''
        self.reset_cursor()
        # First propagate event to symbols for specific treatment
        super(Scene, self).mousePressEvent(event)
        # Store mouse coordinates as possible paste position
        self.click_coordinates = event.scenePos()
        # Enter state machine
        if self.mode == 'idle' and event.button() == Qt.LeftButton:
            # Idle mode: click triggers selection square
            nearby_connection = self.symbol_near(event.scenePos(),
                                                 selectable_only=False)
            connection_selected = False
            if isinstance(nearby_connection, Connection):
                # Click near a connection - forward the event to it
                # (some connections like statechart Edges can react)
                nearby_connection.mousePressEvent(event)
                connection_selected = True
            if not self.symbol_near(event.scenePos(), dist=1):
                self.mode = 'select_items'
                self.orig_pos = event.scenePos()
                self.select_rect = self.addRect(
                        QRectF(self.orig_pos, self.orig_pos))
                if self.context == 'statechart' and not connection_selected:
                    # Specific treatment for statecharts - should subclass
                    for item in self.items():
                        # Remove all Edges control points from the scene
                        try:
                            item.bezier_set_visible(False)
                        except AttributeError:
                            pass

        elif self.mode == 'wait_placement':
            try:
                parent = \
                        self.can_insert(event.scenePos(), self.button_selected)
            except TypeError as err:
                self.messages_window.addItem(str(err))
            else:
                with undoCommands.UndoMacro(self.undo_stack, 'Place Symbol'):
                    item = self.place_symbol(
                            item_type=self.button_selected,
                            parent=parent,
                            pos=event.scenePos() if not parent else None)
            # self.button_selected = None
            self.mode = 'idle'
        elif self.mode == 'wait_connection_source':
            # Check location, and if ok:
            self.mode = 'wait_next_connection_point'
            # if not OK, reset and:
            self.mode = 'idle'


    # pylint: disable=C0103
    def mouseMoveEvent(self, event):
        ''' Handle Click + Mouse move, based on the mode '''
        if event.buttons() == Qt.NoButton or self.mode == 'idle':
            return super(Scene, self).mouseMoveEvent(event)
        elif self.mode == 'select_items':
            rect = QRectF(self.orig_pos, event.scenePos())
            self.select_rect.setRect(rect.normalized())
        elif self.mode == 'wait_next_connection_point':
            # Update the line
            pass


    def quick_menu(self, pos, rect):
        ''' Add actions on the fly to the context-dependent menu that is
        displayed when the user draws a box on the screen '''
        menu       = QtGui.QMenu('Select item to add')
        singletons = (i.__class__ for i in self.visible_symb if i.is_singleton)
        candidates = filter(lambda x: not x.needs_parent
                                      and not x in singletons,
                            ACTIONS.get(self.context, []))

        def add_symbol(sort, rect):
            symb = self.place_symbol(sort, parent=None, pos=rect.topLeft())
            if symb.default_size == "any":
                symb.resize_item(rect)

        def setup_action(sort):
            name   = sort.__name__
            icon   = QtGui.QIcon(':icons/{}.png'.format(name.lower()))
            action = menu.addAction(icon, name)
            action.triggered.connect(partial(add_symbol,
                                             sort,
                                             rect=rect))
        if map(setup_action, candidates):
            menu.exec_(pos)

    # pylint: disable=C0103
    def mouseReleaseEvent(self, event):
        if self.mode == 'select_items':
            found = False
            rect = self.select_rect.rect()
            self.clear_highlight()
            for item in self.items(rect, mode=Qt.ContainsItemBoundingRect):
                try:
                    item.select()
                    self.highlight(item)
                except AttributeError:
                    pass
                else:
                    found = True
            if not found and rect.width() > 20 and rect.height() > 20:
                self.quick_menu(event.screenPos(), rect)
            #self.removeItem(self.select_rect)
            # XXX stop with removeItem, it provokes segfault
            self.select_rect.hide()
        self.mode = 'idle'
        super(Scene, self).mouseReleaseEvent(event)


    # pylint: disable=C0103
    def keyPressEvent(self, event):
        ''' Handle keyboard: Delete, Undo/Redo '''
        super(Scene, self).keyPressEvent(event)
        if event.matches(QtGui.QKeySequence.Delete) and self.selectedItems():
            self.delete_selected_symbols()
            self.clearSelection()
            self.clear_highlight()
            self.clear_focus()
        elif event.matches(QtGui.QKeySequence.Undo):
            if not isinstance(self.focusItem(), EditableText):
                LOG.debug('UNDO ' + self.undo_stack.undoText())
                self.undo_stack.undo()
                self.clearSelection()
                self.clear_highlight()
                self.refresh()
                # Emit a selection change to make sure the toolbar is updated
                # (e.g. when Undoing a Place START symbol)
                self.selectionChanged.emit()
                self.clear_focus()
        elif event.matches(QtGui.QKeySequence.Redo):
            if not isinstance(self.focusItem(), EditableText):
                LOG.debug('REDO ' + self.undo_stack.redoText())
                self.undo_stack.redo()
                self.clearSelection()
                self.clear_highlight()
                self.refresh()
                self.clear_focus()
                # Emit a selection change to make sure the toolbar is updated
                self.selectionChanged.emit()
        elif event.matches(QtGui.QKeySequence.Copy):
            if not isinstance(self.focusItem(), EditableText):
                try:
                    self.copy_selected_symbols()
                except TypeError:
                    LOG.error('Cannot copy')
        elif event.matches(QtGui.QKeySequence.Cut):
            self.cut_selected_symbols()
        elif event.matches(QtGui.QKeySequence.Paste):
            if not isinstance(self.focusItem(), EditableText):
                self.paste_symbols()
                self.refresh()
                self.clear_focus()
        elif event.key() == Qt.Key_N:
            # n to select the next item in a search (vim mode)
            if self.focusItem():
                # Only active when no item has keyboard focus
                return
            try:
                self.clearSelection()
                self.clear_highlight()
                item = self.search_item.next()
                item.select()
                self.highlight(item)
                item.ensureVisible()
            except StopIteration:
                LOG.info('No more matches')
                self.search(self.search_pattern)
            except AttributeError:
                LOG.info('No search pattern set. Use "/<pattern>"')
        elif (event.key() == Qt.Key_J and
                event.modifiers() == Qt.ControlModifier):
            # Debug mode
            for selection in self.selected_symbols:
                LOG.info(unicode(selection))
                LOG.info('Position: ' + str(selection.pos()))
                LOG.info('ScenePos: ' + str(selection.scenePos()))
                LOG.info('BoundingRect: ' + str(selection.boundingRect()))
                LOG.info('ChildrenBoundingRect: ' +
                        str(selection.childrenBoundingRect()))
                pprint.pprint(selection.__dict__, None, 2, 1)
            code.interact('type your command:', local=locals())


if __name__ == '__main__':
    ''' Run from command line '''
    pass
