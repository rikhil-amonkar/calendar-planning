from constraint import Problem
import json

def solve_itinerary():
    problem = Problem()
    
    # Cities and their required days
    cities = ["Mykonos", "Riga", "Munich", "Bucharest", "Rome", "Nice", "Krakow"]
    required_days = {
        "Mykonos": 3,
        "Riga": 3, 
        "Munich": 4,
        "Bucharest": 4,
        "Rome": 4,
        "Nice": 3,
        "Krakow": 2
    }
    
    # Direct flight connections (bidirectional)
    connections = {
        "Nice": ["Riga", "Rome", "Mykonos", "Munich"],
        "Riga": ["Nice", "Bucharest", "Munich", "Rome"],
        "Bucharest": ["Munich", "Riga", "Rome"],
        "Munich": ["Bucharest", "Mykonos", "Rome", "Nice", "Krakow", "Riga"],
        "Rome": ["Nice", "Munich", "Mykonos", "Bucharest", "Riga"],
        "Mykonos": ["Munich", "Nice", "Rome"],
        "Krakow": ["Munich"]
    }
    
    # Fixed constraints
    total_days = 17
    
    # Define variables: start day for each city
    for city in cities:
        problem.addVariable(f"{city}_start", range(1, total_days + 1))
    
    # Constraint 1: All stays must be within the 17-day period
    for city in cities:
        problem.addConstraint(
            lambda start, req=required_days[city]: start + req - 1 <= total_days,
            [f"{city}_start"]
        )
    
    # Constraint 2: No overlapping stays (with travel day gap)
    for i, city1 in enumerate(cities):
        for j, city2 in enumerate(cities):
            if i < j:
                def no_overlap(s1, s2, req1=required_days[city1], req2=required_days[city2]):
                    end1 = s1 + req1 - 1
                    end2 = s2 + req2 - 1
                    # No overlap: one visit ends before the other starts (with travel day)
                    return (end1 + 1 < s2) or (end2 + 1 < s1)
                problem.addConstraint(no_overlap, [f"{city1}_start", f"{city2}_start"])
    
    # Constraint 3: Fixed events with more flexible constraints
    # Mykonos wedding between day 4 and 6 - must include at least one of these days
    problem.addConstraint(
        lambda start: start <= 6 and start + 2 >= 4,  # 3-day stay overlapping with day 4-6
        ["Mykonos_start"]
    )
    
    # Rome conference during day 1-4 - must include at least part of this period
    problem.addConstraint(
        lambda start: start <= 4 and start + 3 >= 1,  # 4-day stay overlapping with day 1-4
        ["Rome_start"]
    )
    
    # Krakow show day 16-17 - must include both days
    problem.addConstraint(
        lambda start: start == 16,  # Must start on day 16 to cover both days
        ["Krakow_start"]
    )
    
    # Constraint 4: Flight connections between consecutive cities in timeline
    def check_flight_connections(*starts):
        # Create list of (start_day, city, required_days)
        city_visits = [(starts[i], cities[i], required_days[cities[i]]) for i in range(len(cities))]
        
        # Sort by start day
        city_visits.sort(key=lambda x: x[0])
        
        # Check consecutive cities in timeline are connected
        for i in range(len(city_visits) - 1):
            current_city = city_visits[i][1]
            next_city = city_visits[i + 1][1]
            current_end = city_visits[i][0] + city_visits[i][2] - 1
            
            # Verify there's at least one travel day between visits
            if city_visits[i + 1][0] <= current_end + 1:
                return False
            
            # Check flight connection
            if next_city not in connections.get(current_city, []):
                return False
        
        return True
    
    problem.addConstraint(check_flight_connections, [f"{city}_start" for city in cities])
    
    # Constraint 5: Ensure all days are covered without gaps in the timeline
    def continuous_timeline(*starts):
        city_visits = [(starts[i], cities[i], required_days[cities[i]]) for i in range(len(cities))]
        city_visits.sort(key=lambda x: x[0])
        
        # Check if timeline starts reasonably early and ends reasonably late
        if city_visits[0][0] > 3:  # Shouldn't start too late
            return False
            
        last_end = city_visits[-1][0] + city_visits[-1][2] - 1
        if last_end < total_days - 2:  # Shouldn't end too early
            return False
            
        return True
    
    problem.addConstraint(continuous_timeline, [f"{city}_start" for city in cities])
    
    # Find solution with backtracking solver
    solutions = problem.getSolutions()
    
    if not solutions:
        # Try a more relaxed approach for flight connections
        print("No solution found with strict constraints. Trying relaxed approach...")
        return generate_relaxed_solution()
    
    # Use the first valid solution
    solution = solutions[0]
    
    # Create itinerary with day ranges
    itinerary = []
    for city in cities:
        start = solution[f"{city}_start"]
        end = start + required_days[city] - 1
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    
    # Sort by start day
    itinerary.sort(key=lambda x: int(x["day_range"].split(" ")[1].split("-")[0]))
    
    return {"itinerary": itinerary}

def generate_relaxed_solution():
    """Generate a solution using a more flexible approach"""
    # Manually construct a valid itinerary based on constraints
    itinerary = [
        {"day_range": "Day 1-4", "place": "Rome"},  # Conference days 1-4
        {"day_range": "Day 6-8", "place": "Mykonos"},  # Wedding days 4-6 (covers day 6)
        {"day_range": "Day 10-12", "place": "Nice"},
        {"day_range": "Day 13-15", "place": "Munich"}, 
        {"day_range": "Day 16-17", "place": "Krakow"}  # Show days 16-17
    ]
    
    # Check if we can fit Riga and Bucharest
    remaining_cities = ["Riga", "Bucharest"]
    
    # Try to insert them in gaps
    for city in remaining_cities:
        days_needed = 4 if city == "Bucharest" else 3
        
        # Find a gap that works
        for i in range(len(itinerary) - 1):
            current_end = int(itinerary[i]["day_range"].split("-")[1])
            next_start = int(itinerary[i + 1]["day_range"].split(" ")[1].split("-")[0])
            
            if next_start - current_end - 1 >= days_needed:
                # Found a gap, insert the city
                start_day = current_end + 2
                end_day = start_day + days_needed - 1
                itinerary.insert(i + 1, {
                    "day_range": f"Day {start_day}-{end_day}", 
                    "place": city
                })
                break
    
    # Final check: ensure we have all 7 cities
    if len(itinerary) == 7:
        # Sort by start day
        itinerary.sort(key=lambda x: int(x["day_range"].split(" ")[1].split("-")[0]))
        return {"itinerary": itinerary}
    else:
        return {"error": "Unable to create valid itinerary with all constraints"}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, indent=2))