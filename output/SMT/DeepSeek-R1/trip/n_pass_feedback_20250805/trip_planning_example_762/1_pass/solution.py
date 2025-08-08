from z3 import *
import json

def main():
    # Map cities to integers: 
    # 0: Dublin, 1: Madrid, 2: Oslo, 3: London, 4: Vilnius, 5: Berlin
    city_names = {
        0: "Dublin",
        1: "Madrid",
        2: "Oslo",
        3: "London",
        4: "Vilnius",
        5: "Berlin"
    }
    
    # Required days for each city (by integer code)
    days_arr = [3, 2, 3, 2, 3, 5]
    
    # Define the permutation variables: 6 Ints for the order
    perm = [Int('p%d' % i) for i in range(6)]
    s = Solver()
    
    # Each perm[i] must be between 0 and 5 and all distinct
    for i in range(6):
        s.add(And(perm[i] >= 0, perm[i] <= 5))
    s.add(Distinct(perm))
    
    # Define the allowed direct flight pairs (both orders)
    original_pairs = [
        (3,1), # London and Madrid
        (2,4), # Oslo and Vilnius
        (5,4), # Berlin and Vilnius
        (1,2), # Madrid and Oslo
        (1,0), # Madrid and Dublin
        (3,2), # London and Oslo
        (1,5), # Madrid and Berlin
        (5,2), # Berlin and Oslo
        (0,2), # Dublin and Oslo
        (3,0), # London and Dublin
        (3,5), # London and Berlin
        (5,0)  # Berlin and Dublin
    ]
    allowed_pairs = []
    for a, b in original_pairs:
        allowed_pairs.append((a, b))
        allowed_pairs.append((b, a))
    
    # Constraint: consecutive cities in the permutation must be in allowed_pairs
    for i in range(5):
        s.add(Or([And(perm[i] == a, perm[i+1] == b) for (a, b) in allowed_pairs]))
    
    # Helper function to get the days for a city (Z3 compatible)
    def get_day(city):
        return If(city == 0, days_arr[0],
                If(city == 1, days_arr[1],
                If(city == 2, days_arr[2],
                If(city == 3, days_arr[3],
                If(city == 4, days_arr[4],
                If(city == 5, days_arr[5], 0))))))
    
    # Define cumulative sums
    cum0 = get_day(perm[0])
    cum1 = cum0 + get_day(perm[1])
    cum2 = cum1 + get_day(perm[2])
    cum3 = cum2 + get_day(perm[3])
    cum4 = cum3 + get_day(perm[4])
    cum5 = cum4 + get_day(perm[5])
    s.add(cum5 == 18)  # total days accounted (13 days + 5 travel days)
    
    # Find the indices for Dublin (0), Madrid (1), Berlin (5) in the permutation
    j_D = If(perm[0] == 0, 0, 
            If(perm[1] == 0, 1,
            If(perm[2] == 0, 2,
            If(perm[3] == 0, 3,
            If(perm[4] == 0, 4,
            If(perm[5] == 0, 5, -1))))))
    
    j_M = If(perm[0] == 1, 0, 
            If(perm[1] == 1, 1,
            If(perm[2] == 1, 2,
            If(perm[3] == 1, 3,
            If(perm[4] == 1, 4,
            If(perm[5] == 1, 5, -1))))))
    
    j_B = If(perm[0] == 5, 0, 
            If(perm[1] == 5, 1,
            If(perm[2] == 5, 2,
            If(perm[3] == 5, 3,
            If(perm[4] == 5, 4,
            If(perm[5] == 5, 5, -1))))))
    
    s.add(j_D >= 0, j_M >= 0, j_B >= 0)
    
    # Function to get the start day for a city at index j
    def get_start(j):
        return If(j == 0, 1,
                If(j == 1, cum0,
                If(j == 2, cum1 - 1,
                If(j == 3, cum2 - 2,
                If(j == 4, cum3 - 3,
                If(j == 5, cum4 - 4, -1))))))
    
    # Function to get the end day for a city at index j
    def get_end(j):
        return If(j == 0, cum0,
                If(j == 1, cum1 - 1,
                If(j == 2, cum2 - 2,
                If(j == 3, cum3 - 3,
                If(j == 4, cum4 - 4,
                If(j == 5, cum5 - 5, -1))))))
    
    # Event constraints
    start_D = get_start(j_D)
    end_D = get_end(j_D)
    s.add(start_D <= 9, end_D >= 7)  # Dublin: between day 7 and 9
    
    start_M = get_start(j_M)
    end_M = get_end(j_M)
    s.add(start_M <= 3, end_M >= 2)  # Madrid: between day 2 and 3
    
    start_B = get_start(j_B)
    end_B = get_end(j_B)
    s.add(start_B <= 7, end_B >= 3)  # Berlin: between day 3 and 7
    
    # Check and get the model
    if s.check() == sat:
        m = s.model()
        perm_val = [m.evaluate(perm[i]).as_long() for i in range(6)]
        print("Permutation:", [city_names[p] for p in perm_val])
        
        # Evaluate the cumulative sums in the model
        def eval_z3_expr(expr):
            return m.evaluate(expr, model_completion=True).as_long()
        
        cum0_val = eval_z3_expr(cum0)
        cum1_val = eval_z3_expr(cum1)
        cum2_val = eval_z3_expr(cum2)
        cum3_val = eval_z3_expr(cum3)
        cum4_val = eval_z3_expr(cum4)
        cum5_val = eval_z3_expr(cum5)
        
        # Boundaries (end_i for segments 0 to 4)
        boundaries = [
            cum0_val,        # end0 = cum0 - 0
            cum1_val - 1,    # end1 = cum1 - 1
            cum2_val - 2,    # end2 = cum2 - 2
            cum3_val - 3,    # end3 = cum3 - 3
            cum4_val - 4     # end4 = cum4 - 4
        ]
        # The last boundary is end5 = cum5 - 5 = 13, which is fixed.
        
        itinerary = []
        for d in range(1, 14):  # days 1 to 13
            if d in boundaries:
                i = boundaries.index(d)
                # On travel day d: in both city i and city i+1
                cities = [perm_val[i], perm_val[i+1]]
                city_list = [city_names[c] for c in cities]
                itinerary.append({"day": d, "city": city_list})
            else:
                if d < boundaries[0]:
                    city_idx = perm_val[0]
                elif d < boundaries[1]:
                    city_idx = perm_val[1]
                elif d < boundaries[2]:
                    city_idx = perm_val[2]
                elif d < boundaries[3]:
                    city_idx = perm_val[3]
                elif d < boundaries[4]:
                    city_idx = perm_val[4]
                else:
                    city_idx = perm_val[5]
                itinerary.append({"day": d, "city": [city_names[city_idx]]})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()