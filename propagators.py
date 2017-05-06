

#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented to complete problem solution.  
import queue
import itertools

'''This file will contain different constraint propagators to be used within 
   bt_search.

   propagator == a function with the following template
      propagator(csp, newVar=None)
           ==> returns (True/False, [(Variable, Value), (Variable, Value) ...]

      csp is a CSP object---the propagator can use this to get access
      to the variables and constraints of the problem. The assigned variables
      can be accessed via methods, the values assigned can also be accessed.

      newVar (newly instaniated variable) is an optional argument.
      if newVar is not None:
          then newVar is the most
           recently assigned variable of the search.
      else:
          progator is called before any assignments are made
          in which case it must decide what processing to do
           prior to any variables being assigned. SEE BELOW

       The propagator returns True/False and a list of (Variable, Value) pairs.
       Return is False if a deadend has been detected by the propagator.
       in this case bt_search will backtrack
       return is true if we can continue.

      The list of variable values pairs are all of the values
      the propagator pruned (using the variable's prune_value method). 
      bt_search NEEDS to know this in order to correctly restore these 
      values when it undoes a variable assignment.

      NOTE propagator SHOULD NOT prune a value that has already been 
      pruned! Nor should it prune a value twice

      PROPAGATOR called with newVar = None
      PROCESSING REQUIRED:
        for plain backtracking (where we only check fully instantiated 
        constraints) 
        we do nothing...return true, []

        for forward checking (where we only check constraints with one
        remaining variable)
        we look for unary constraints of the csp (constraints whose scope 
        contains only one variable) and we forward_check these constraints.

        for gac we establish initial GAC by initializing the GAC queue
        with all constaints of the csp


      PROPAGATOR called with newVar = a variable V
      PROCESSING REQUIRED:
         for plain backtracking we check all constraints with V (see csp method
         get_cons_with_var) that are fully assigned.

         for forward checking we forward check all constraints with V
         that have one unassigned variable left

         for gac we initialize the GAC queue with all constraints containing V.
   '''

def prop_BT(csp, newVar=None):
    '''Do plain backtracking propagation. That is, do no 
    propagation at all. Just check fully instantiated constraints'''
    
    #seems like picking a varaible and looping through & assigning each variable
    #in its domain is done outside this function
    #this only checks the constraints
    
    if not newVar:
        return True, []
    for c in csp.get_cons_with_var(newVar): 
        '''return list of constraints that include var in their scope'''
        if c.get_n_unasgn() == 0: 
            '''return the number of unassigned variables in the constraint's scope'''
            vals = []
            vars = c.get_scope()
            '''get list of variables the constraint is over'''
            for var in vars:
                vals.append(var.get_assigned_value())
                '''return assigned value...returns None if is unassigned'''
            if not c.check(vals):
                '''Given list of values, one for each variable in the
                constraints scope, return true if and only if these value
                assignments satisfy the constraint by applying the
                constraints "satisfies" function.  Note the list of values
                are must be ordered in the same order as the list of
                variables in the constraints scope'''
                return False, []
    return True, []

def FCCheck(c):
           #since newVar was newly instantiated, we do a forward checking on that variable

    
    #return True if DWO
    #these constraints have all but one unassigned
    #find the unassigned variable X and go through its curdomain.
    unassignedX = c.get_unasgn_vars()[0]
    # ASSUMPTION IS THAT UNASSIGNED IS NOT A LIST #
    cur_domain = unassignedX.cur_domain()
    for d in cur_domain: 
        unassignedX.assign(d) #assign the value
        
        vals = [] #use the same method as above to check 
        vars = c.get_scope()
        for var in vars:
            vals.append(var.get_assigned_value()) 
        #print(c.check(vals))
        if not c.check(vals):
            pruned_list.append([unassignedX,d])
            unassignedX.prune_value(d) #prune the value
        unassignedX.unassign() #unassign it so we can test the other ones
    if unassignedX.cur_domain_size() == 0:
        #unassignedX.restore_curdom() #restore all pruned
        # for i in range(len(list)):
        #     unassignedX.unprune_value(list[i][1])
        return True #DWO
    else: #at least one variable satisfies all the constraints
        #unassignedX.restore_curdom() #restore all pruned
        # for i in range(len(list)):
        #     unassignedX.unprune_value(list[i][1])
        return False

    

def prop_FC(csp, newVar=None):
    '''Do forward checking. That is check constraints with 
       only one uninstantiated variable. Remember to keep 
       track of all pruned variable,value pairs and return '''
    DWOoccured = False
    global pruned_list
    pruned_list = [] #keep track of pruned 
    
    if newVar==None: #forward checks all constraints
        '''we look for unary constraints of the csp (constraints whose scope 
        contains only one variable) and we forward_check these constraints.'''
        for c in csp.get_all_cons():
            #returns list of all constraints
            #since we only do forward checking on constraints with only one variable remaining, unary constraints need to be checked, by definition
            vars = c.get_scope() 
            '''get list of variables the constraint is over'''
            if len(vars) == 1:
                result = FCCheck(c)
                if result: #FCCheck == True = DWO
                    DWOoccured = True
                    return False, pruned_list
                    #break #stop checking constraints, already failed
                            #one constraint
        if not DWOoccured: #all constraints satisfied OR no unary constraints
            return True, pruned_list #no dead-end found
                        
    if newVar != None: #forward checks 
        '''for forward checking we forward check all constraints with V
            that have one unassigned variable left'''
        for c in csp.get_cons_with_var(newVar): #loop through constraints
            #return list of constraints containing newVar
            #check which constraints have only one unassigned variable
            if c.get_n_unasgn() == 1:
                result = FCCheck(c)
                if result:
                    DW0occured = True
                    return False, pruned_list
                    #break
        if DWOoccured == False:
            return True, pruned_list

def find_assignment(C):
    flag = False
    #loop through all the unassigned constraint v
    list_domain = [] #a list of lists, each list contains the curr_dom of a var
    for var in C.get_scope():
        list_domain.append(var.cur_domain())
    list_product = list(itertools.product(*list_domain)) 
    #cartesian product (all permutations), a list of n-tuple's
    for combination in list_product:
        assignment = list(combination) #convert n-tuple to list
        if C.check(assignment):
            flag = True #there is at least one assignment that works
    return flag
            
            
def GAC_Enforce(csp):
    while not GACQueue.empty():
        C=GACQueue.get()
        constraint_var = C.get_scope() 
        for var in constraint_var:
            if var.is_assigned():
                continue
            for d in var.cur_domain():
                #check if unassigned. some will be assigned already since
                #we're looping through all the variables in the scope
                #if assigned, we shouldn't modify it in any way since 
                #it was assigned as newVal outside of function.

                #var.assign(d) #assign, need to unassign later
                #if not find_assignment(C):
                if not C.has_support(var,d):
                    pruned_list1.append((var, d))
                    var.prune_value(d) #prune it
                    #var.unassign()
                    if var.cur_domain_size() == 0:
                        #empty queue since it's global
                        return False #that means DWO   
                    else:
                        for new_constraint in csp.get_cons_with_var(var):
                            if new_constraint not in GACQueue.queue:
                                GACQueue.put(new_constraint)                         
                        
    return True #no DWO
                
def prop_GAC(csp, newVar=None):
    '''Do GAC propagation. If newVar is None we do initial GAC enforce 
       processing all constraints. Otherwise we do GAC enforce with
       constraints containing newVar on GAC Queue'''

    '''PROPAGATOR called with newVar = None
        for gac we establish initial GAC by initializing the GAC queue
        with all constaints of the csp
        
      PROPAGATOR called with newVar = a variable V
      PROCESSING REQUIRED:
    for gac we initialize the GAC queue with all constraints containing V.'''
    global GACQueue
    global pruned_list1 #prune list
    pruned_list1 = []
    GACQueue = queue.Queue()
    if newVar == None: #preprocessing step where no var has been instantiated
        for c in csp.get_all_cons():
            GACQueue.put(c) #add constraint to queue
        if GAC_Enforce(csp): #return True, no DWO
            return True, pruned_list1
        else:
            return False, pruned_list1
    if newVar != None:
        for c in csp.get_cons_with_var(newVar):
            GACQueue.put(c)
        if GAC_Enforce(csp):
            return True, pruned_list1
        else:
            return False, pruned_list1
            
            


    
    
    
    
    
    

