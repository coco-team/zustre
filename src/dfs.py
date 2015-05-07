##
## Generic DFS
##

# User-defined exceptions for dfs handlers

class DFS_DontSearchSucc (Exception) :
  """to be used in a visit handler to return without searching successors
  """
  pass

class DFS_SearchCompletedPrematurely (Exception) :
  """to be used in a visit/done handler to indicate termination of search
prematurely, i.e. before exploring the entire graph
  """
  def __init__ (self, val=None) :
    self.val = val


class DFS (object) :
  def __init__ (self, key, succ) :
    self.key = key # key function for nodes
    self.succ = succ # successor function

    self.visited = list () # list of visited nodes
    self.done  = set () # set of nodes done with dfs

    # handlers and args
    self.handlers = list ()
    self.handlerUserArgNames = list () # user-defined argnames
    self.handlerUserArgs = dict () # from user-defined argnames to values

    # handler ids
    self.VISIT = None
    self.REVISIT = None
    self.BACKEDGE = None
    self.DONE = None

  def setVisited (self, node) :
    self.visited.append (self.key (node))

  def _getId (self, node) :
    k = self.key (node)
    return self.visited.index (k)

  def setDone (self, node) :
    self.done.add (self.key (node))
  
  def isDone (self, node) :
    return (self.key (node) in self.done)
  
  def isVisited (self, node) :
    return (self.key (node) in self.visited)
  
  def isBackEdge (self, fro, to) :
    return ((self._getId (to) <= self._getId (fro)) and \
            not self.isDone (to))

  def addHandler (self, handler, userArgNames, tp) :
    handler_id = len (self.handlers)
    if tp == 'visit' :
      self.VISIT = handler_id
    elif tp == 'revisit' :
      self.REVISIT = handler_id
    elif tp == 'backedge' :
      self.BACKEDGE = handler_id
    elif tp == 'done' :
      self.DONE = handler_id

    self.handlers.append (handler)
    self.handlerUserArgNames.append (userArgNames)

  def handle (self, handler_id, *default_args) :
    # find out handler and args
    handler = self.handlers [handler_id]
    userArgNames = self.handlerUserArgNames [handler_id]
    args = list (default_args) + \
           [self.handlerUserArgs [name] for name in userArgNames]
    # call the handler
    d = handler (*args)
    # update handlerUserArgs
    if d != None :
      for key,val in d.items() :
        self.handlerUserArgs [key] = val

  def search (self, root) :
    self.setVisited (root)
    if self.VISIT != None :
      try :
        self.handle (self.VISIT, root)
      except DFS_DontSearchSucc :
        return
    for node in self.succ (root) :
      if self.isVisited (node) :
        if self.REVISIT != None :
          self.handle (self.REVISIT, node)
        if self.BACKEDGE != None :
          if self.isBackEdge (root, node) :
            self.handle (self.BACKEDGE, root, node)
      else :
        self.search (node)
    self.setDone (root)
    if self.DONE != None :
      self.handle (self.DONE, root)

  def getValueOfArg (self, argname) :
    return self.handlerUserArgs [argname]

  def setInitValue (self, argname, val) :
    self.handlerUserArgs [argname] = val
