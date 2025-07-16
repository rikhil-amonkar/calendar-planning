import json

def solve_itinerary():
    cities = ['Valencia', 'Athens', 'Naples', 'Zurich']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    direct_flights = [
        (0, 1), (1, 0),  # Valencia <-> Athens
        (0, 2), (2, 0),  # Valencia <-> Naples
        (1, 2), (2, 1),  # Athens <-> Naples
        (1, 3), (3, 1),  # Athens <-> Zurich
        (2, 3), (3, 2),  # Naples <-> Zurich
        (0, 3), (3, 0)   # Valencia <-> Zurich
    ]
    
    total_days = 20
    required_days = [6, 6, 5, 6]  # Valencia, Athens, Naples, Zurich
    
    # Precompute flight connections
    flight_connections = {i: [] for i in range(4)}
    for a, b in direct_flights:
        flight_connections[a].append(b)
        flight_connections[b].append(a)
    
    # Initialize the schedule
    schedule = [None] * total_days
    
    def backtrack(day, city_counts):
        if day == total_days:
            # Check if all city days are met
            if all(city_counts[i] == required_days[i] for i in range(4)):
                return True
            return False
        
        # Try to stay in the current city if possible
        current_city = schedule[day-1] if day > 0 else None
        if current_city is not None:
            if city_counts[current_city] < required_days[current_city]:
                schedule[day] = current_city
                city_counts[current_city] += 1
                if backtrack(day + 1, city_counts):
                    return True
                city_counts[current_city] -= 1
                schedule[day] = None
        
        # Try to fly to connected cities
        if day > 0:
            for next_city in flight_connections[current_city]:
                if city_counts[next_city] < required_days[next_city]:
                    schedule[day] = next_city
                    city_counts[next_city] += 1
                    if backtrack(day + 1, city_counts):
                        return True
                    city_counts[next_city] -= 1
                    schedule[day] = None
        else:
            # First day, can start in any city
            for city in range(4):
                if city_counts[city] < required_days[city]:
                    schedule[day] = city
                    city_counts[city] += 1
                    if backtrack(day + 1, city_counts):
                        return True
                    city_counts[city] -= 1
                    schedule[day] = None
        return False
    
    # Additional constraints for Athens and Naples
    def meets_constraints(schedule):
        # Athens between day 1 and day 6 (0-5 in zero-based)
        if not any(schedule[d] == 1 for d in range(6)):
            return False
        # Naples between day 16 and 20 (15-19 in zero-based)
        if not any(schedule[d] == 2 for d in range(15, 20)):
            return False
        return True
    
    # Find a valid schedule
    city_counts = [0, 0, 0, 0]
    if backtrack(0, city_counts):
        if meets_constraints(schedule):
            # Build the itinerary
            itinerary = []
            current_city = schedule[0]
            start_day = 1  # 1-based
            
            for d in range(1, total_days):
                if schedule[d] != schedule[d-1]:
                    # Flight occurs between d-1 and d (1-based days d and d+1)
                    # Add the departure city's stay up to d (1-based day d)
                    end_day = d  # 1-based
                    if start_day == end_day:
                        itinerary.append({"day_range": f"Day {start_day}", "place": cities[current_city]})
                    else:
                        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": cities[current_city]})
                    # Add the flight day entries for both cities
                    itinerary.append({"day_range": f"Day {end_day}", "place": cities[current_city]})
                    itinerary.append({"day_range": f"Day {end_day}", "place": cities[schedule[d]]})
                    # Update current city and start day
                    current_city = schedule[d]
                    start_day = end_day + 1  # since end_day is the day of flight
                # else continue the current city
            # Add the last segment
            end_day = total_days
            if start_day == end_day:
                itinerary.append({"day_range": f"Day {start_day}", "place": cities[current_city]})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": cities[current_city]})
            
            return {"itinerary": itinerary}
    
    return {"error": "No valid itinerary found"}

# Solve and print the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))