import json
from constraint import Problem, AllDifferentConstraint

def solve_itinerary():
    # Define the problem
    problem = Problem()
    
    # Cities and their required days
    cities = {
        "Manchester": 3,
        "Istanbul": 7,
        "Venice": 7,
        "Krakow": 6,
        "Lyon": 2
    }
    
    total_days = 21
    
    # Direct flight connections
    connections = {
        "Manchester": ["Venice", "Istanbul", "Krakow"],
        "Venice": ["Manchester", "Istanbul", "Lyon"],
        "Istanbul": ["Manchester", "Venice", "Krakow", "Lyon"],
        "Krakow": ["Istanbul", "Manchester"],
        "Lyon": ["Venice", "Istanbul"]
    }
    
    # Create variables for arrival day for each city
    # We'll represent the itinerary as a sequence of stays
    # Each stay is (city, start_day, end_day)
    
    # We need to find an order of visiting cities that satisfies:
    # 1. Total days = 21
    # 2. Required days in each city
    # 3. Direct flight connections between consecutive cities
    # 4. Wedding in Manchester between day 1-3
    # 5. Workshop in Venice between day 3-9
    
    # Approach: Find all permutations of cities that satisfy connection constraints
    # Then check if we can assign days that satisfy all constraints
    
    def find_valid_sequences(current_sequence, remaining_cities, all_sequences):
        if not remaining_cities:
            all_sequences.append(current_sequence[:])
            return
        
        for city in remaining_cities:
            if not current_sequence or city in connections[current_sequence[-1]]:
                new_remaining = [c for c in remaining_cities if c != city]
                find_valid_sequences(current_sequence + [city], new_remaining, all_sequences)
    
    all_sequences = []
    city_list = list(cities.keys())
    find_valid_sequences([], city_list, all_sequences)
    
    # Check each sequence for feasibility with day constraints
    valid_itineraries = []
    
    for sequence in all_sequences:
        # Try to assign days to this sequence
        day_assignments = [0] * len(sequence)  # start days
        
        def assign_days(idx, current_day):
            if idx == len(sequence):
                # Check if total days match
                last_city_end = current_day + cities[sequence[-1]] - 1
                if last_city_end == total_days:
                    return [(sequence[i], day_assignments[i], day_assignments[i] + cities[sequence[i]] - 1) 
                           for i in range(len(sequence))]
                return None
            
            city = sequence[idx]
            required_days = cities[city]
            
            # Special constraints
            if city == "Manchester":
                # Must be between day 1-3 for wedding
                if current_day > 1:
                    return None
                day_assignments[idx] = 1
                result = assign_days(idx + 1, 1 + required_days)
                if result:
                    return result
                return None
            elif city == "Venice":
                # Workshop between day 3-9
                if current_day > 3 or current_day + required_days - 1 < 9:
                    return None
                day_assignments[idx] = 3
                result = assign_days(idx + 1, 3 + required_days)
                if result:
                    return result
                return None
            else:
                # For other cities, try starting from current_day
                if current_day <= total_days - required_days + 1:
                    day_assignments[idx] = current_day
                    result = assign_days(idx + 1, current_day + required_days)
                    if result:
                        return result
                return None
        
        itinerary = assign_days(0, 1)
        if itinerary:
            valid_itineraries.append(itinerary)
    
    if not valid_itineraries:
        return {"error": "No valid itinerary found"}
    
    # Use the first valid itinerary
    chosen_itinerary = valid_itineraries[0]
    
    # Convert to the required output format
    itinerary_output = []
    for city, start_day, end_day in chosen_itinerary:
        if start_day == end_day:
            day_range = f"Day {start_day}"
        else:
            day_range = f"Day {start_day}-{end_day}"
        itinerary_output.append({
            "day_range": day_range,
            "place": city
        })
    
    return {"itinerary": itinerary_output}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, indent=2))