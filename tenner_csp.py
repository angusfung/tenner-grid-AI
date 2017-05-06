from cspbase import *
import itertools


def binary_not_equal(i,j):
    return i!=j

def nary_sum_check(t,tenner_sum): 
    #t is a tuple
    return sum(t) == tenner_sum
    
    

def tenner_csp_model_1(initial_tenner_board):
    #set up variables array
    
    vars = []
    for i in range(len(initial_tenner_board[0])): #iterate through n (3<n<8)
        inner_vars = [] 
        for j in range(10):
            if initial_tenner_board[0][i][j] == -1:
                dom = [k for k in range(10)]
            else:
                dom = [initial_tenner_board[0][i][j]]
            inner_vars.append(Variable('{}{}'.format(i,j),dom))
        vars.append(inner_vars)
        
    cons = [] #add all constraints in a list, one constraint per cell

            
    #row check
    for i in range(len(initial_tenner_board[0])):
        for j in range(10):
            for k in range(j+1, 10):

                    con = Constraint("C(Q{},Q{})".format(i,j),[vars[i][j],vars[i][k]])
                    sat_tuples = []

                    for t in itertools.product(vars[i][j].cur_domain(), vars[i][k].cur_domain()):   
                        if binary_not_equal(t[0],t[1]):
                            sat_tuples.append(t)
                    con.add_satisfying_tuples(sat_tuples)
                    cons.append(con)

    #adjacent check
    for i in range(len(initial_tenner_board[0])):
        for j in range(10):

            if i!=len(initial_tenner_board[0])-1: #bottom
                sat_tuples = []
                con = Constraint("BotC(Q{},Q{})".format(i,j),[vars[i][j],vars[i+1][j]])
                for t in itertools.product(vars[i][j].cur_domain(), vars[i+1][j].cur_domain()):
                    if binary_not_equal(t[0],t[1]):
                        sat_tuples.append(t)
                con.add_satisfying_tuples(sat_tuples)
                cons.append(con)
                if j!=0: #bottom left
                    sat_tuples = []
                    con = Constraint("BLC(Q{},Q{})".format(i,j),[vars[i][j],vars[i+1][j-1]])
                    for t in itertools.product(vars[i][j].cur_domain(), vars[i+1][j-1].cur_domain()):
                        if binary_not_equal(t[0],t[1]):
                            sat_tuples.append(t)
                    con.add_satisfying_tuples(sat_tuples)
                    cons.append(con)
                if j!=9: #bottom right
                    sat_tuples = []
                    con = Constraint("BRC(Q{},Q{})".format(i,j),[vars[i][j],vars[i+1][j+1]])
                    for t in itertools.product(vars[i][j].cur_domain(), vars[i+1][j+1].cur_domain()):
                        if binary_not_equal(t[0],t[1]):
                            sat_tuples.append(t)
                    con.add_satisfying_tuples(sat_tuples)
                    cons.append(con)
     
    #sum check       
    for i in range(10): #iterate over the columns
        var_scope = []
        sum_tuples = []
        var_dom = []
        for j in range(len(initial_tenner_board[0])):
            var_scope.append(vars[j][i]) #(1,1) (2,1) (3,1), ..., (n,1) etc.
            var_dom.append(vars[j][i].cur_domain())
        con = Constraint("SumC(Q{},Q{})".format(i,j),var_scope)
        dom = [k for k in range(10)]
        n = len(initial_tenner_board[0])
        for t in itertools.product(*var_dom):
            if nary_sum_check(t, initial_tenner_board[1][i]): #column i
                sum_tuples.append(t)
        con.add_satisfying_tuples(sum_tuples)
        cons.append(con)
        
    csp = CSP("Tenner", [value for sublist in vars for value in sublist])
    for c in cons:
        csp.add_constraint(c)
        
    return csp, vars              
            

##############################

def tenner_csp_model_2(initial_tenner_board):
    
    vars = []
    for i in range(len(initial_tenner_board[0])): #iterate through n (3<n<8)
        inner_vars = [] 
        for j in range(10):
            if initial_tenner_board[0][i][j] == -1:
                dom = [k for k in range(10)]
            else:
                dom = [initial_tenner_board[0][i][j]]
            inner_vars.append(Variable('{}{}'.format(i,j),dom))
        vars.append(inner_vars)
    
    
    #row check
    cons = []
    for i in range(len(initial_tenner_board[0])):
        dom = [k for k in range(10)]
        var_scope = []
        sat_tuples = [] 
        for j in range(10):
            if initial_tenner_board[0][i][j] != -1:
                dom.remove(initial_tenner_board[0][i][j]) #make the domain smaller
            else:
                var_scope.append(vars[i][j])
        #print(len(dom)==len(var_scope))
        con = Constraint("C{}".format(i),var_scope)
        for perm in itertools.permutations(dom):
            sat_tuples.append(perm)
        con.add_satisfying_tuples(sat_tuples)
        cons.append(con)
        
    #adjacent check
    for i in range(len(initial_tenner_board[0])):
        for j in range(10):
            if i!=len(initial_tenner_board[0])-1: #bottom
                sat_tuples = []
                con = Constraint("BotC(Q{},Q{})".format(i,j),[vars[i][j],vars[i+1][j]])
                for t in itertools.product(vars[i][j].cur_domain(), vars[i+1][j].cur_domain()):
                    if binary_not_equal(t[0],t[1]):
                        sat_tuples.append(t)
                con.add_satisfying_tuples(sat_tuples)
                cons.append(con)
                if j!=0: #bottom left
                    sat_tuples = []
                    con = Constraint("BLC(Q{},Q{})".format(i,j),[vars[i][j],vars[i+1][j-1]])
                    for t in itertools.product(vars[i][j].cur_domain(), vars[i+1][j-1].cur_domain()):
                        if binary_not_equal(t[0],t[1]):
                            sat_tuples.append(t)
                    con.add_satisfying_tuples(sat_tuples)
                    cons.append(con)
                if j!=9: #bottom right
                    sat_tuples = []
                    con = Constraint("BRC(Q{},Q{})".format(i,j),[vars[i][j],vars[i+1][j+1]])
                    for t in itertools.product(vars[i][j].cur_domain(), vars[i+1][j+1].cur_domain()):
                        if binary_not_equal(t[0],t[1]):
                            sat_tuples.append(t)
                    con.add_satisfying_tuples(sat_tuples)
                    cons.append(con)
     
    #sum check       
    for i in range(10): #iterate over the columns
        var_scope = []
        sum_tuples = []
        var_dom = []
        for j in range(len(initial_tenner_board[0])):
            var_scope.append(vars[j][i]) #(1,1) (2,1) (3,1), ..., (n,1) etc.
            var_dom.append(vars[j][i].cur_domain())
        con = Constraint("SumC(Q{},Q{})".format(i,j),var_scope)
        dom = [k for k in range(10)]
        n = len(initial_tenner_board[0])
        for t in itertools.product(*var_dom):
            if nary_sum_check(t, initial_tenner_board[1][i]): #column i
                sum_tuples.append(t)
        con.add_satisfying_tuples(sum_tuples)
        cons.append(con)
        
    csp = CSP("Tenner", [value for sublist in vars for value in sublist])
    for c in cons:
        csp.add_constraint(c)
        
    return csp, vars         

