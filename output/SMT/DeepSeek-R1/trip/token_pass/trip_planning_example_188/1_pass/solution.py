from z3 import *
import json

def main():
    # Create solver
    s = Solver()
    
    # Cities: Brussels (0), Barcelona (1), Split (2)
    num_days = 12
    num_cities = 3
    overnight = [Int(f'overnight_{i}') for i in range(13)]  # indices 0 to 12
    
    # Constraint: overnight[0] = Brussels (0)
    s.add(overnight[0] == 0)
    
    # Constraint: overnight[1] must be Brussels (0) because we must be in Brussels on day2 morning
    s.add(overnight[1] == 0)
    
    # Each overnight must be between 0 and 2
    for i in range(13):
        s.add(overnight[i] >= 0, overnight[i] <= 2)
    
    # Allowed transitions: only direct flights
    for i in range(1, 13):
        prev = overnight[i-1]
        curr = overnight[i]
        # If city changes, must be allowed flight
        s.add(If(prev != curr, 
                 Or(And(prev == 0, curr == 1),
                    And(prev == 1, curr == 0),
                    And(prev == 1, curr == 2),
                    And(prev == 2, curr == 1)),
                 True))
    
    # Calculate days per city
    brussels_count = 0
    barcelona_count = 0
    split_count = 0
    
    for i in range(1, 13):  # days 1 to 12
        prev_city = overnight[i-1]
        curr_city = overnight[i]
        # Brussels
        brussels_count += If(Or(prev_city == 0, curr_city == 0), 1, 0)
        # Barcelona
        barcelona_count += If(Or(prev_city == 1, curr_city == 1), 1, 0)
        # Split
        split_count += If(Or(prev_city == 2, curr_city == 2), 1, 0)
    
    # Add constraints for total days in each city
    s.add(brussels_count == 2)
    s.add(barcelona_count == 7)
    s.add(split_count == 5)
    
    # Check if feasible
    if s.check() == sat:
        m = s.model()
        # Get the overnight values
        ov_values = [m.evaluate(overnight[i]).as_long() for i in range(13)]
        
        # Map city numbers to names
        city_map = {0: 'Brussels', 1: 'Barcelona', 2: 'Split'}
        
        # Determine the set of cities for each day (1 to 12)
        daily_cities = []
        for i in range(1, 13):
            prev = ov_values[i-1]
            curr = ov_values[i]
            if prev == curr:
                cities = [city_map[prev]]
            else:
                cities = sorted([city_map[prev], city_map[curr]])
            daily_cities.append(cities)
        
        # Group consecutive days with the same set of cities
        itinerary = []
        start_day = 1
        current_set = daily_cities[0]
        
        for day in range(2, 13):  # day is the next day index (2-based)
            if daily_cities[day-1] == current_set:
                continue
            else:
                end_day = day - 1
                if start_day == end_day:
                    day_range = f"Day {start_day}"
                else:
                    day_range = f"Day {start_day}-{end_day}"
                itinerary.append({"day_range": day_range, "place": ", ".join(current_set)})
                start_day = day
                current_set = daily_cities[day-1]
        
        # Add the last segment
        if start_day <= num_days:
            end_day = num_days
            if start_day == end_day:
                day_range = f"Day {start_day}"
            else:
                day_range = f"Day {start_day}-{end_day}"
            itinerary.append({"day_range": day_range, "place": ", ".join(current_set)})
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()