
# Basically removes var from each clause if in it, or reports if unsat
# Create new formula with var assigned to value
def update_formula(clauses, var):
    new_clauses = []
    for clause in clauses:
        if var in clause:
            new_clause = []
            new_clauses.append(new_clause)
        elif -var in clause:
            new_clause = []
            for cvar in clause:
                if cvar == -var:
                    continue
                else:
                    new_clause.append(cvar)
            if len(new_clause) == 0:
                return clauses, 'UNSAT'
            new_clauses.append(new_clause)
        else:
            new_clauses.append(clause)
    done = True
    for clause in new_clauses:
        if len(clause) > 0:
            done = False
            break
    if done:
        return new_clauses, 'SAT'
    return new_clauses, 'UNKNOWN'

def get_bad_clause(clauses, var):
    for idx, clause in enumerate(clauses):
        if var in clause:
            continue
        elif -var in clause:
            # Just contains -var
            # See above in update_formula when UNSAT returned
            if len(set(clause)) == 1:
                return idx
    return None