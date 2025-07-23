from z3 import *
import json

def main():
    # Mapping cities to integer IDs
    city2id = {
        "Reykjavik": 0,
        "Riga": 1,
        "Oslo": 2,
        "Lyon": 3,
        "Dubrovnik": 4,
        "Madrid": 5,
        "Warsaw": 6,
        "London": 7
    }
    id2city = {v: k for k, v in city2id.items()}
    
    # Days required for each city (by ID)
    days_arr = [4, 2, 3, 5, 2, 2, 4, 3]
    
    # Build directed flight edges
    bidirectional_city_pairs = [
        ("Warsaw", "Reykjavik"),
        ("Oslo", "Madrid"),
        ("Warsaw", "Riga"),
        ("Lyon", "London"),
        ("Madrid", "London"),
        ("Warsaw", "London"),
        ("Warsaw", "Oslo"),
        ("Oslo", "Dubrovnik"),
        ("Oslo", "Reykjavik"),
        ("Riga", "Oslo"),
        ("Oslo", "Lyon"),
        ("Oslo", "London"),
        ("London", "Reykjavik"),
        ("Warsaw", "Madrid"),
        ("Madrid", "Lyon"),
        ("Dubrovnik", "Madrid")
    ]
    
    directed_edges_set = set()
    for (a, b) in bidirectional_city_pairs:
        id_a = city2id[a]
        id_b = city2id[b]
        directed_edges_set.add((id_a, id_b))
        directed_edges_set.add((id_b, id_a))
    
    # Add unidirectional flight from Reykjavik to Madrid
    directed_edges_set.add((city2id["Reykjavik"], city2id["Madrid"]))
    
    # Create Z3 solver and variables
    s = Solver()
    
    # order[i] is the city ID at position i in the itinerary
    order = [Int('order_%d' % i) for i in range(8)]
    # Each order[i] must be between 0 and 7
    for i in range(8):
        s.add(order[i] >= 0, order[i] < 8)
    s.add(Distinct(order))
    
    # Arrays for start and end days of each position
    start = [Int('start_%d' % i) for i in range(8)]
    end = [Int('end_%d' % i) for i in range(8)]
    
    # Constraints for the first city
    s.add(start[0] == 1)
    s.add(end[0] == start[0] + days_arr[order[0]] - 1)
    
    # Constraints for the remaining cities
    for i in range(1, 8):
        s.add(start[i] == end[i-1])
        s.add(end[i] == start[i] + days_arr[order[i]] - 1)
    
    # The trip must end on day 18
    s.add(end[7] == 18)
    
    # Flight constraints between consecutive cities
    allowed_edges_ids = list(directed_edges_set)
    for i in range(7):
        conds = []
        for (a, b) in allowed_edges_ids:
            conds.append(And(order[i] == a, order[i+1] == b))
        s.add(Or(conds))
    
    # Constraint for Riga (city ID 1): must include day 4 or 5
    riga_conds = []
    for k in range(8):
        # If the city at position k is Riga (ID 1)
        cond1 = And(order[k] == 1, start[k] <= 4, 4 <= end[k])
        cond2 = And(order[k] == 1, start[k] <= 5, 5 <= end[k])
        riga_conds.append(Or(cond1, cond2))
    s.add(Or(riga_conds))
    
    # Constraint for Dubrovnik (city ID 4): must include day 7 or 8
    dub_conds = []
    for k in range(8):
        cond1 = And(order[k] == 4, start[k] <= 7, 7 <= end[k])
        cond2 = And(order[k] == 4, start[k] <= 8, 8 <= end[k])
        dub_conds.append(Or(cond1, cond2))
    s.add(Or(dub_conds))
    
    # Check and get the model
    if s.check() == sat:
        m = s.model()
        
        # Build the itinerary
        itinerary = []
        
        # For each day from 1 to 18, check which cities are active
        for day in range(1, 19):
            for pos in range(8):
                city_id = m.evaluate(order[pos]).as_long()
                city_name = id2city[city_id]
                start_day = m.evaluate(start[pos]).as_long()
                end_day = m.evaluate(end[pos]).as_long()
                if start_day <= day <= end_day:
                    itinerary.append({"day": day, "city": city_name})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()