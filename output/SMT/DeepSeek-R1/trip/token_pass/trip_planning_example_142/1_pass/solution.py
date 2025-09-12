import json
from z3 import *

def main():
    # Cities: Madrid (0), Dublin (1), Tallinn (2)
    cities = {0: "Madrid", 1: "Dublin", 2: "Tallinn"}
    n_days = 7
    n_cities = 3
    
    # Create solver
    s = Solver()
    
    # end_city[i] represents the city at the end of day i (0-indexed days, 0 is start of trip)
    end_city = [Int(f"end_city_{i}") for i in range(n_days+1)]
    
    # Constraint: end_city values must be between 0 and 2
    for i in range(n_days+1):
        s.add(And(end_city[i] >= 0, end_city[i] < n_cities))
    
    # Constraint: travel must be via direct flights only
    for d in range(1, n_days+1):
        s.add(Or(
            end_city[d] == end_city[d-1],  # stay in same city
            And(end_city[d-1] == 0, end_city[d] == 1),  # Madrid <-> Dublin
            And(end_city[d-1] == 1, end_city[d] == 0),
            And(end_city[d-1] == 1, end_city[d] == 2),  # Dublin <-> Tallinn
            And(end_city[d-1] == 2, end_city[d] == 1)
        ))
    
    # Compute presence for each city each day
    presences = []
    for d in range(1, n_days+1):
        day_presence = []
        for c in range(n_cities):
            # Presence defined as being in city at start or end of day
            day_presence.append(Or(end_city[d-1] == c, end_city[d] == c))
        presences.append(day_presence)
    
    # Constraint: total days in each city
    madrid_days = Sum([If(presences[d][0], 1, 0) for d in range(n_days)])
    dublin_days = Sum([If(presences[d][1], 1, 0) for d in range(n_days)])
    tallinn_days = Sum([If(presences[d][2], 1, 0) for d in range(n_days)])
    
    s.add(madrid_days == 4)
    s.add(dublin_days == 3)
    s.add(tallinn_days == 2)
    
    # Constraint: workshop in Tallinn on days 6 and 7 (1-indexed days 6-7)
    s.add(Or(end_city[5] == 2, end_city[6] == 2))  # Present on day 6
    s.add(Or(end_city[6] == 2, end_city[7] == 2))  # Present on day 7
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        # Get end_city values
        end_values = [m.evaluate(end_city[i]).as_long() for i in range(n_days+1)]
        
        # Compute presence matrix (day, city)
        presence_matrix = []
        for d in range(1, n_days+1):
            day_presence = []
            for c in range(n_cities):
                day_presence.append(
                    end_values[d-1] == c or end_values[d] == c
                )
            presence_matrix.append(day_presence)
        
        # Find contiguous intervals for each city
        intervals = []
        for c in range(n_cities):
            city_days = []
            for d in range(n_days):
                if presence_matrix[d][c]:
                    city_days.append(d+1)  # 1-indexed days
            
            if not city_days:
                continue
                
            # Group consecutive days
            current_start = city_days[0]
            current_end = city_days[0]
            for i in range(1, len(city_days)):
                if city_days[i] == current_end + 1:
                    current_end = city_days[i]
                else:
                    intervals.append((current_start, current_end, c))
                    current_start = city_days[i]
                    current_end = city_days[i]
            intervals.append((current_start, current_end, c))
        
        # Sort intervals by start day
        intervals.sort(key=lambda x: x[0])
        
        # Format output
        itinerary = []
        for start, end, c in intervals:
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": cities[c]})
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()