from z3 import *

def main():
    # Initialize solver
    solver = Solver()
    
    # Define variables
    a = Int('a')
    b = Int('b')
    order = Int('order')  # 0 for Krakow->Paris->Seville, 1 for Seville->Paris->Krakow
    
    # Constraints on variables
    solver.add(1 <= a, a < b, b <= 10)
    solver.add(Or(order == 0, order == 1))
    
    # City day constraints
    krakow_days = If(order == 0, a + 1, 11 - b)
    paris_days = (b - a) + 1
    seville_days = If(order == 0, 11 - b, a + 1)
    
    solver.add(krakow_days == 5)
    solver.add(paris_days == 2)
    solver.add(seville_days == 6)
    
    # Workshop constraint: Krakow must include at least one day between 1-5
    solver.add(If(order == 1, b + 1 <= 5, True))
    
    # Check satisfiability
    if solver.check() == sat:
        model = solver.model()
        a_val = model[a].as_long()
        b_val = model[b].as_long()
        order_val = model[order].as_long()
        
        if order_val == 0:
            itinerary = [
                {"day_range": f"Day 1-{a_val+1}", "place": "Krakow"},
                {"day_range": f"Day {a_val+1}-{b_val+1}", "place": "Paris"},
                {"day_range": f"Day {b_val+1}-11", "place": "Seville"}
            ]
        else:
            itinerary = [
                {"day_range": f"Day 1-{a_val+1}", "place": "Seville"},
                {"day_range": f"Day {a_val+1}-{b_val+1}", "place": "Paris"},
                {"day_range": f"Day {b_val+1}-11", "place": "Krakow"}
            ]
        
        # Output as JSON
        import json
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()