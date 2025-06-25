from z3 import *

def main():
    # Define the positions for the first four cities
    pos0, pos1, pos2, pos3 = Ints('pos0 pos1 pos2 pos3')
    pos = [pos0, pos1, pos2, pos3]
    
    s = Solver()
    
    # Each position must be between 0 and 3 (inclusive)
    for p in pos:
        s.add(p >= 0, p <= 3)
    
    s.add(Distinct(pos0, pos1, pos2, pos3))
    
    # Create a Z3 array for the days each city requires
    days_arr = Array('days_arr', IntSort(), IntSort())
    days_arr = Store(days_arr, 0, 5)  # Porto
    days_arr = Store(days_arr, 1, 4)  # Prague
    days_arr = Store(days_arr, 2, 4)  # Reykjavik
    days_arr = Store(days_arr, 3, 4)  # Munich
    
    # Get the days for each position
    day0 = days_arr[pos0]
    day1 = days_arr[pos1]
    day2 = days_arr[pos2]
    day3 = days_arr[pos3]
    
    # Calculate start and end days for each city in the sequence
    s0 = 1
    e0 = s0 + day0 - 1
    s1 = e0
    e1 = s1 + day1 - 1
    s2 = e1
    e2 = s2 + day2 - 1
    s3 = e2
    e3 = s3 + day3 - 1
    
    # The last day of the fourth city must be day 14 (to fly to Amsterdam)
    s.add(e3 == 14)
    
    # Function to get the start day of a specific city (by index) in the sequence
    def get_start(city_idx):
        return If(pos0 == city_idx, s0,
               If(pos1 == city_idx, s1,
               If(pos2 == city_idx, s2,
               s3)))
    
    # Fixed durations for each city index
    durations = {0: 5, 1: 4, 2: 4, 3: 4}
    
    # Constraints for Reykjavik (index 2) and Munich (index 3)
    # For Reykjavik: must have at least one day between 4 and 7
    Reykjavik_idx = 2
    Reykjavik_start = get_start(Reykjavik_idx)
    Reykjavik_end = Reykjavik_start + durations[Reykjavik_idx] - 1
    s.add(Or(
        And(Reykjavik_start <= 4, 4 <= Reykjavik_end),
        And(Reykjavik_start <= 5, 5 <= Reykjavik_end),
        And(Reykjavik_start <= 6, 6 <= Reykjavik_end),
        And(Reykjavik_start <= 7, 7 <= Reykjavik_end)
    ))
    
    # For Munich: must have at least one day between 7 and 10
    Munich_idx = 3
    Munich_start = get_start(Munich_idx)
    Munich_end = Munich_start + durations[Munich_idx] - 1
    s.add(Or(
        And(Munich_start <= 7, 7 <= Munich_end),
        And(Munich_start <= 8, 8 <= Munich_end),
        And(Munich_start <= 9, 9 <= Munich_end),
        And(Munich_start <= 10, 10 <= Munich_end)
    ))
    
    # Allowed direct flight pairs (undirected)
    allowed_pairs = [
        (0, 3), (3, 0),  # Porto and Munich
        (1, 2), (2, 1),  # Prague and Reykjavik
        (1, 3), (3, 1),  # Prague and Munich
        (2, 3), (3, 2)   # Reykjavik and Munich
    ]
    
    # Constraints for consecutive cities to have direct flights
    for i in range(3):
        cons = []
        for a, b in allowed_pairs:
            cons.append(And(pos[i] == a, pos[i+1] == b))
        s.add(Or(cons))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        order = [m.evaluate(p).as_long() for p in pos]
        city_names = ["Porto", "Prague", "Reykjavik", "Munich"]
        first_four = [city_names[idx] for idx in order]
        cities = first_four + ["Amsterdam", "Santorini"]
        
        # Calculate start and end days for the first four cities
        days_fixed = [5, 4, 4, 4]  # Porto, Prague, Reykjavik, Munich
        durations = [days_fixed[idx] for idx in order]
        starts = [1] * 4
        ends = [0] * 4
        starts[0] = 1
        ends[0] = starts[0] + durations[0] - 1
        for i in range(1, 4):
            starts[i] = ends[i-1]
            ends[i] = starts[i] + durations[i] - 1
        
        # Fixed days for Amsterdam and Santorini
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