from z3 import *

def main():
    # Initialize solver
    s = Optimize()
    
    # Start time variables (in minutes from 9:00 AM)
    s_n = Int('s_n')
    s_m = Int('s_m')
    s_j = Int('s_j')
    
    # Boolean variables for whether we meet each friend
    nancy_met = Bool('nancy_met')
    mary_met = Bool('mary_met')
    jessica_met = Bool('jessica_met')
    
    # Boolean variables for meeting order
    b_nm = Bool('b_nm')  # True: Nancy before Mary
    b_nj = Bool('b_nj')  # True: Nancy before Jessica
    b_mj = Bool('b_mj')  # True: Mary before Jessica
    
    # Constraints for Nancy
    c1 = Implies(nancy_met, And(s_n >= 30, s_n <= 180))  # 30 to 180 minutes (90 min meeting)
    
    # Constraints for Mary
    c2 = Implies(mary_met, And(s_m >= 17, s_m <= 645))  # 17 to 645 minutes (75 min meeting)
    
    # Constraints for Jessica
    c3 = Implies(jessica_met, And(s_j >= 135, s_j <= 240))  # 135 to 240 minutes (45 min meeting)
    
    # Pairwise constraints for Nancy and Mary
    c4 = Implies(And(nancy_met, mary_met),
                 Or(
                     And(b_nm, s_m >= s_n + 90 + 17),  # Nancy -> Mary: CT to AS (17 min)
                     And(Not(b_nm), s_n >= s_m + 75 + 16)  # Mary -> Nancy: AS to CT (16 min)
                 ))
    
    # Pairwise constraints for Nancy and Jessica
    c5 = Implies(And(nancy_met, jessica_met),
                 Or(
                     And(b_nj, s_j >= s_n + 90 + 22),  # Nancy -> Jessica: CT to BV (22 min)
                     And(Not(b_nj), s_n >= s_j + 45 + 18)  # Jessica -> Nancy: BV to CT (18 min)
                 ))
    
    # Pairwise constraints for Mary and Jessica
    c6 = Implies(And(mary_met, jessica_met),
                 Or(
                     And(b_mj, s_j >= s_m + 75 + 16),  # Mary -> Jessica: AS to BV (16 min)
                     And(Not(b_mj), s_m >= s_j + 45 + 16)  # Jessica -> Mary: BV to AS (16 min)
                 ))
    
    # Transitivity constraint when all three are met
    c7 = Implies(And(nancy_met, mary_met, jessica_met),
                 Or(
                    And(b_nm, b_nj, b_mj),        # Order: N, M, J
                    And(b_nm, b_nj, Not(b_mj)),    # Order: N, J, M
                    And(Not(b_nm), b_nj, b_mj),    # Order: M, N, J
                    And(Not(b_nm), Not(b_nj), b_mj), # Order: M, J, N
                    And(b_nm, Not(b_nj), Not(b_mj)), # Order: J, N, M
                    And(Not(b_nm), Not(b_nj), Not(b_mj))  # Order: J, M, N
                 )
    
    # Add all constraints
    s.add(c1, c2, c3, c4, c5, c6, c7)
    
    # Objective: maximize the number of meetings
    total_met = If(nancy_met, 1, 0) + If(mary_met, 1, 0) + If(jessica_met, 1, 0)
    s.maximize(total_met)
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        print("SOLUTION:")
        print(f"Nancy met: {model.evaluate(nancy_met)}")
        if model.evaluate(nancy_met):
            start_n = model.evaluate(s_n)
            print(f"  Start time: {start_n} minutes after 9:00 AM")
        print(f"Mary met: {model.evaluate(mary_met)}")
        if model.evaluate(mary_met):
            start_m = model.evaluate(s_m)
            print(f"  Start time: {start_m} minutes after 9:00 AM")
        print(f"Jessica met: {model.evaluate(jessica_met)}")
        if model.evaluate(jessica_met):
            start_j = model.evaluate(s_j)
            print(f"  Start time: {start_j} minutes after 9:00 AM")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()