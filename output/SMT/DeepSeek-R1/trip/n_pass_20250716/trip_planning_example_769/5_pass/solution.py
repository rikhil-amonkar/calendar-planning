from z3 import *

def main():
    # Define positions for first four cities
    pos0, pos1, pos2, pos3 = Ints('pos0 pos1 pos2 pos3')
    pos = [pos0, pos1, pos2, pos3]
    
    s = Solver()
    
    # Each position must be between 0-3 (city indices)
    for p in pos:
        s.add(p >= 0, p <= 3)
    s.add(Distinct(pos0, pos1, pos2, pos3))
    
    # Days required for each city
    days_arr = Array('days_arr', IntSort(), IntSort())
    days_arr = Store(days_arr, 0, 5)  # Porto
    days_arr = Store(days_arr, 1, 4)  # Prague
    days_arr = Store(days_arr, 2, 4)  # Reykjavik
    days_arr = Store(days_arr, 3, 4)  # Munich
    
    # Get days for each position
    day0 = days_arr[pos0]
    day1 = days_arr[pos1]
    day2 = days_arr[pos2]
    day3 = days_arr[pos3]
    
    # Calculate start/end days
    s0 = 1
    e0 = s0 + day0 - 1
    s1 = e0
    e1 = s1 + day1 - 1
    s2 = e1
    e2 = s2 + day2 - 1
    s3 = e2
    e3 = s3 + day3 - 1
    
    # Last day must be 14 (to fly to Amsterdam)
    s.add(e3 == 14)
    
    # Function to get start day of a city
    def get_start(city_idx):
        return If(pos0 == city_idx, s0,
               If(pos1 == city_idx, s1,
               If(pos2 == city_idx, s2,
               s3)))
    
    # Fixed durations for each city
    durations = {0: 5, 1: 4, 2: 4, 3: 4}
    
    # Reykjavik must fully contain days 4-7
    Reykjavik_idx = 2
    Reykjavik_start = get_start(Reykjavik_idx)
    Reykjavik_end = Reykjavik_start + durations[Reykjavik_idx] - 1
    s.add(Reykjavik_start <= 4, Reykjavik_end >= 7)
    
    # Munich must fully contain days 7-10
    Munich_idx = 3
    Munich_start = get_start(Munich_idx)
    Munich_end = Munich_start + durations[Munich_idx] - 1
    s.add(Munich_start <= 7, Munich_end >= 10)
    
    # Allowed direct flight pairs
    allowed_pairs = [
        (0, 3), (3, 0),  # Porto-Munich
        (1, 2), (2, 1),  # Prague-Reykjavik
        (1, 3), (3, 1),  # Prague-Munich
        (2, 3), (3, 2)   # Reykjavik-Munich
    ]
    
    # Consecutive cities must have direct flights
    for i in range(3):
        cons = []
        for a, b in allowed_pairs:
            cons.append(And(pos[i] == a, pos[i+1] == b))
        s.add(Or(cons))
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        order = [m.evaluate(p).as_long() for p in pos]
        city_names = ["Porto", "Prague", "Reykjavik", "Munich"]
        first_four = [city_names[idx] for idx in order]
        cities = first_four + ["Amsterdam", "Santorini"]
        
        # Calculate start/end days
        days_fixed = [5, 4, 4, 4]
        durations = [days_fixed[idx] for idx in order]
        starts = [1] * 4
        ends = [0] * 4
        starts[0] = 1
        ends[0] = starts[0] + durations[0] - 1
        for i in range(1, 4):
            starts[i] = ends[i-1]
            ends[i] = starts[i] + durations[i] - 1
        
        # Fixed Amsterdam/Santorini days
        starts.append(14)  # Amsterdam
        ends.append(15)    # Amsterdam
        starts.append(15)  # Santorini
        ends.append(16)    # Santorini
        
        # Build itinerary
        itinerary = []
        for i in range(6):
            city = cities[i]
            s_day = starts[i]
            e_day = ends[i]
            if s_day == e_day:
                itinerary.append({"day_range": f"Day {s_day}", "place": city})
            else:
                itinerary.append({"day_range": f"Day {s_day}-{e_day}", "place": city})
            
            if i < 5:
                itinerary.append({"day_range": f"Day {e_day}", "place": city})
                itinerary.append({"day_range": f"Day {e_day}", "place": cities[i+1]})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()