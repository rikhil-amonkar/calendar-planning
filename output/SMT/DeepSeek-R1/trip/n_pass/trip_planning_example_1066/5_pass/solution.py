from z3 import *

def solve_itinerary():
    s = Solver()
    cities = ["Stuttgart", "Split", "Helsinki", "Brussels", "Bucharest", "London", "Mykonos", "Madrid"]
    
    # Create Z3 variables for the city indices of the 5 segments
    seg0 = Int('seg0')
    seg1 = Int('seg1')
    seg2 = Int('seg2')
    seg3 = Int('seg3')
    seg4 = Int('seg4')
    seg_city = [seg0, seg1, seg2, seg3, seg4]
    
    # Fix the first and last segments
    s.add(seg0 == 0)  # Stuttgart
    s.add(seg4 == 7)  # Madrid
    
    # Middle segments must be from the remaining cities (indices 1 to 6)
    for i in range(1, 4):
        s.add(seg_city[i] >= 1, seg_city[i] <= 6)
    
    # All segments must have distinct cities
    s.add(Distinct(seg_city))
    
    if s.check() == sat:
        m = s.model()
        day_ranges = ["Day 1-4", "Day 6-9", "Day 11-14", "Day 16-19", "Day 21"]
        itinerary = []
        for i in range(5):
            city_index = m.evaluate(seg_city[i]).as_long()
            itinerary.append({
                "day_range": day_ranges[i],
                "place": cities[city_index]
            })
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    print(result)
else:
    print("No valid itinerary found.")