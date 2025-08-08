from z3 import Solver, Int, Distinct, Or, And, sat
import json

def main():
    cities = ["Nice", "Krakow", "Dublin", "Lyon", "Frankfurt"]
    n = len(cities)
    city_to_index = {city: idx for idx, city in enumerate(cities)}
    
    allowed_flights = [
        ("Nice", "Dublin"),
        ("Dublin", "Frankfurt"),
        ("Dublin", "Krakow"),
        ("Krakow", "Frankfurt"),
        ("Lyon", "Frankfurt"),
        ("Nice", "Frankfurt"),
        ("Lyon", "Dublin"),
        ("Nice", "Lyon")
    ]
    allowed_directed = set()
    for a, b in allowed_flights:
        a_idx = city_to_index[a]
        b_idx = city_to_index[b]
        allowed_directed.add((a_idx, b_idx))
        allowed_directed.add((b_idx, a_idx))
    
    s = Solver()
    
    # Block assignments: block0 = Nice, block4 = Frankfurt
    block1 = Int('block1')
    block2 = Int('block2')
    block3 = Int('block3')
    
    # Constraints for blocks 1-3: distinct cities from {Krakow, Dublin, Lyon}
    s.add(block1 >= 1, block1 <= 3)
    s.add(block2 >= 1, block2 <= 3)
    s.add(block3 >= 1, block3 <= 3)
    s.add(Distinct(block1, block2, block3))
    
    # Nice (block0) must connect to Dublin (2) or Lyon (3) for block1
    s.add(Or(block1 == 2, block1 == 3))
    
    # Flight constraints between consecutive blocks
    flight_constr_12 = []
    flight_constr_23 = []
    flight_constr_34 = []
    for (a, b) in allowed_directed:
        flight_constr_12.append(And(block1 == a, block2 == b))
        flight_constr_23.append(And(block2 == a, block3 == b))
        if b == 4:  # Flight to Frankfurt (block4)
            flight_constr_34.append(block3 == a)
    s.add(Or(flight_constr_12))
    s.add(Or(flight_constr_23))
    s.add(Or(flight_constr_34))  # Block3 must connect to Frankfurt
    
    if s.check() == sat:
        model = model = s.model()
        b1 = model[block1].as_long()
        b2 = model[block2].as_long()
        b3 = model[block3].as_long()
        block_cities = [city_to_index["Nice"], b1, b2, b3, city_to_index["Frankfurt"]]
        
        # Durations: Nice=5, Krakow=6, Dublin=7, Lyon=4, Frankfurt=2
        durations = [
            5,
            7 if b1 == 2 else (4 if b1 == 3 else 6),  # b1: Dublin=7, Lyon=4
            7 if b2 == 2 else (6 if b2 == 1 else 4),  # b2: Dublin=7, Krakow=6, Lyon=4
            7 if b3 == 2 else (6 if b3 == 1 else 4),  # b3: Dublin=7, Krakow=6, Lyon=4
            2
        ]
        
        # Compute start and end days
        starts = [1]
        ends = [5]  # Nice ends on day 5
        for i in range(1, 5):
            starts.append(ends[i-1])  # Next block starts same day previous ends
            ends.append(starts[i] + durations[i] - 1)
        
        # Build itinerary
        itinerary = []
        for i in range(5):
            day_range = f"Day {starts[i]}-{ends[i]}"
            place = cities[block_cities[i]]
            itinerary.append({"day_range": day_range, "place": place})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()