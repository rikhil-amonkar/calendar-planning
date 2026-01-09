import json

def solve_itinerary():
    # Define the problem
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
    
    # Find all valid sequences that satisfy connection constraints
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
        # Try different starting days for Manchester
        for manchester_start in range(1, 4):  # Manchester must start between day 1-3
            if manchester_start + cities["Manchester"] - 1 > 3:  # Must end by day 3
                continue
                
            # Try different starting days for Venice
            for venice_start in range(3, 10):  # Venice must start between day 3-9
                if venice_start + cities["Venice"] - 1 > 9:  # Must end by day 9
                    continue
                
                # Create a day assignment for this sequence
                day_assignments = {}
                day_assignments["Manchester"] = manchester_start
                day_assignments["Venice"] = venice_start
                
                # Check if this sequence can work with these fixed assignments
                current_day = 1
                itinerary = []
                valid = True
                
                for city in sequence:
                    if city in day_assignments:
                        start_day = day_assignments[city]
                        # Check if we can reach this city by the required start day
                        if start_day < current_day:
                            valid = False
                            break
                        # Add travel days if needed
                        if start_day > current_day:
                            # We have gap days - this is allowed
                            current_day = start_day
                    else:
                        # For other cities, start as soon as possible
                        start_day = current_day
                    
                    end_day = start_day + cities[city] - 1
                    if end_day > total_days:
                        valid = False
                        break
                    
                    itinerary.append((city, start_day, end_day))
                    current_day = end_day + 1  # Next day after leaving
                
                if valid and current_day - 1 <= total_days:
                    # Check if all constraints are satisfied
                    manchester_ok = False
                    venice_ok = False
                    
                    for city, start, end in itinerary:
                        if city == "Manchester":
                            if start >= 1 and end <= 3:
                                manchester_ok = True
                        if city == "Venice":
                            if start >= 3 and end <= 9:
                                venice_ok = True
                    
                    if manchester_ok and venice_ok:
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