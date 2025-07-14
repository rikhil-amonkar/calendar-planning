import json
from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Reykjavik": 2,
        "Stockholm": 2,
        "Porto": 5,
        "Nice": 3,
        "Venice": 4,
        "Vienna": 3,
        "Split": 3,
        "Copenhagen": 2
    }
    
    # Direct flights (undirected)
    direct_flights = {
        ("Copenhagen", "Vienna"),
        ("Nice", "Stockholm"),
        ("Split", "Copenhagen"),
        ("Nice", "Reykjavik"),
        ("Nice", "Porto"),
        ("Reykjavik", "Vienna"),
        ("Stockholm", "Copenhagen"),
        ("Nice", "Venice"),
        ("Nice", "Vienna"),
        ("Reykjavik", "Copenhagen"),
        ("Nice", "Copenhagen"),
        ("Stockholm", "Vienna"),
        ("Venice", "Vienna"),
        ("Copenhagen", "Porto"),
        ("Reykjavik", "Stockholm"),
        ("Stockholm", "Split"),
        ("Split", "Vienna"),
        ("Copenhagen", "Venice"),
        ("Vienna", "Porto")
    }
    
    # Make the flights bidirectional
    flights = set()
    for a, b in direct_flights:
        flights.add((a, b))
        flights.add((b, a))
    direct_flights = flights
    
    # Create a dictionary for quick lookup of connected cities
    connected = {}
    city_list = list(cities.keys())
    for city in city_list:
        connected[city] = []
        for other in city_list:
            if (city, other) in direct_flights:
                connected[city].append(other)
    
    # Z3 variables: for each day (1..17), which city are we in?
    Day = 17
    s = Solver()
    city_vars = [[Bool(f"Day_{day+1}_{city}") for city in city_list] for day in range(Day)]
    
    # Each day, exactly one city is visited
    for day in range(Day):
        s.add(Or([city_vars[day][i] for i in range(len(city_list))]))
        # No two cities on the same day
        for i in range(len(city_list)):
            for j in range(i+1, len(city_list)):
                s.add(Not(And(city_vars[day][i], city_vars[day][j])))
    
    # Constraint: total days per city must match requirements
    for city_idx, city in enumerate(city_list):
        total_days = Sum([If(city_vars[day][city_idx], 1, 0) for day in range(Day)])
        s.add(total_days == cities[city])
    
    # Flight constraints: consecutive days in different cities must have a direct flight
    for day in range(Day - 1):
        for city1_idx in range(len(city_list)):
            for city2_idx in range(len(city_list)):
                if city1_idx != city2_idx:
                    city1 = city_list[city1_idx]
                    city2 = city_list[city2_idx]
                    if (city1, city2) not in direct_flights:
                        s.add(Not(And(city_vars[day][city1_idx], city_vars[day+1][city2_idx])))
    
    # Event constraints:
    # Reykjavik: 2 days, meet between day 3 and 4. So must be in Reykjavik on day 3 or 4.
    reykjavik_idx = city_list.index("Reykjavik")
    s.add(Or(city_vars[2][reykjavik_idx], city_vars[3][reykjavik_idx]))
    
    # Stockholm: 2 days, meet between day 4 and 5. So must be in Stockholm on day 4 or 5.
    stockholm_idx = city_list.index("Stockholm")
    s.add(Or(city_vars[3][stockholm_idx], city_vars[4][stockholm_idx]))
    
    # Porto: 5 days, wedding between day 13 and 17. So must be in Porto on at least one of days 13-17 (indices 12-16).
    porto_idx = city_list.index("Porto")
    s.add(Or([city_vars[day][porto_idx] for day in range(12, 17)]))
    
    # Vienna: 3 days, workshop between day 11 and 13. So must be in Vienna on at least one of days 11-13 (indices 10-12).
    vienna_idx = city_list.index("Vienna")
    s.add(Or([city_vars[day][vienna_idx] for day in range(10, 13)]))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        # Determine the sequence of cities from the model
        sequence = []
        for day in range(Day):
            for city_idx in range(len(city_list)):
                if m.evaluate(city_vars[day][city_idx]):
                    sequence.append((day + 1, city_list[city_idx]))  # days are 1-based
        
        # Generate day ranges for the itinerary
        itinerary = []
        i = 0
        n = len(sequence)
        while i < n:
            current_day, current_city = sequence[i]
            j = i
            while j < n and sequence[j][1] == current_city and sequence[j][0] == current_day + (j - i):
                j += 1
            end_day = sequence[j-1][0] if j > i else current_day
            if current_day == end_day:
                itinerary.append({"day_range": f"Day {current_day}", "place": current_city})
            else:
                itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": current_city})
            i = j
        
        # Now, handle flight days (days with two cities)
        # Reconstruct the sequence with flight transitions
        detailed_sequence = []
        for day in range(Day):
            day_num = day + 1
            current_cities = []
            for city_idx in range(len(city_list)):
                if m.evaluate(city_vars[day][city_idx]):
                    current_cities.append(city_list[city_idx])
            if len(current_cities) == 1:
                detailed_sequence.append((day_num, current_cities[0]))
            else:
                # This shouldn't happen due to constraints, but handle just in case
                for city in current_cities:
                    detailed_sequence.append((day_num, city))
        
        # Now, process detailed_sequence to find transitions
        full_itinerary = []
        i = 0
        while i < len(detailed_sequence):
            day, city = detailed_sequence[i]
            if i + 1 < len(detailed_sequence) and detailed_sequence[i+1][0] == day:
                # Flight day
                next_city = detailed_sequence[i+1][1]
                full_itinerary.append({"day_range": f"Day {day}", "place": city})
                full_itinerary.append({"day_range": f"Day {day}", "place": next_city})
                i += 2
            else:
                # Single city day or part of a multi-day stay
                j = i
                while j < len(detailed_sequence) and detailed_sequence[j][1] == city and (j == i or detailed_sequence[j][0] == detailed_sequence[j-1][0] + 1):
                    j += 1
                start_day = detailed_sequence[i][0]
                end_day = detailed_sequence[j-1][0] if j > i else start_day
                if start_day == end_day:
                    full_itinerary.append({"day_range": f"Day {start_day}", "place": city})
                else:
                    full_itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
                i = j
        
        return {"itinerary": full_itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))