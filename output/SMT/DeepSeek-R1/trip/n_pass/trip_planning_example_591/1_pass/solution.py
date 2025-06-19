from z3 import *
import json

def main():
    s_G, s_M, s_B, s_V, s_S = Ints('s_G s_M s_B s_V s_S')
    e_G = s_G + 3  # Geneva: 4 days
    e_M = s_M + 6  # Munich: 7 days
    e_B = s_B + 1  # Bucharest: 2 days
    e_V = s_V + 5  # Valencia: 6 days
    e_S = s_S + 1  # Stuttgart: 2 days

    solver = Solver()

    # Geneva constraints: must be within [1,4]
    solver.add(s_G >= 1, e_G <= 4)
    
    # Munich constraints: must cover [4,10]
    solver.add(s_M <= 4, e_M >= 10)
    
    # Sequence constraints (flight connections)
    solver.add(e_G == s_M)  # Fly from Geneva to Munich on day 4
    solver.add(e_M == s_B)  # Fly from Munich to Bucharest on day 10
    solver.add(e_B == s_V)  # Fly from Bucharest to Valencia on day 11
    solver.add(e_V == s_S)  # Fly from Valencia to Stuttgart on day 16
    
    # Total trip must be 17 days
    min_start = Min(s_G, s_M, s_B, s_V, s_S)
    max_end = Max(e_G, e_M, e_B, e_V, e_S)
    solver.add(min_start == 1, max_end == 17)
    
    if solver.check() == sat:
        model = solver.model()
        s_G_val = model[s_G].as_long()
        s_M_val = model[s_M].as_long()
        s_B_val = model[s_B].as_long()
        s_V_val = model[s_V].as_long()
        s_S_val = model[s_S].as_long()
        
        s_val = {
            'Geneva': s_G_val,
            'Munich': s_M_val,
            'Bucharest': s_B_val,
            'Valencia': s_V_val,
            'Stuttgart': s_S_val
        }
        
        e_val = {
            'Geneva': s_val['Geneva'] + 3,
            'Munich': s_val['Munich'] + 6,
            'Bucharest': s_val['Bucharest'] + 1,
            'Valencia': s_val['Valencia'] + 5,
            'Stuttgart': s_val['Stuttgart'] + 1
        }
        
        route = ['Geneva', 'Munich', 'Bucharest', 'Valencia', 'Stuttgart']
        itinerary = []
        
        for i, city in enumerate(route):
            start = s_val[city]
            end = e_val[city]
            if i > 0:
                itinerary.append({"day_range": f"Day {start}", "place": city})
            itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
            if i < len(route) - 1:
                itinerary.append({"day_range": f"Day {end}", "place": city})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()