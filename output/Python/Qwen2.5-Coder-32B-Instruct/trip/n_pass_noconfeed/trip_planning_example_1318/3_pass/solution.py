import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Oslo": {"days": 2, "meet_friend": (24, 25)},
        "Helsinki": {"days": 2},
        "Edinburgh": {"days": 3},
        "Riga": {"days": 2},
        "Tallinn": {"days": 5, "wedding": (4, 8)},
        "Budapest": {"days": 5},
        "Vilnius": {"days": 5},
        "Porto": {"days": 5},
        "Geneva": {"days": 4}
    }
    
    # Define the flight connections
    flights = [
        ("Porto", "Oslo"), ("Edinburgh", "Budapest"), ("Edinburgh", "Geneva"),
        ("Riga", "Tallinn"), ("Edinburgh", "Porto"), ("Vilnius", "Helsinki"),
        ("Tallinn", "Vilnius"), ("Riga", "Oslo"), ("Geneva", "Oslo"),
        ("Edinburgh", "Oslo"), ("Edinburgh", "Helsinki"), ("Vilnius", "Oslo"),
        ("Riga", "Helsinki"), ("Budapest", "Geneva"), ("Helsinki", "Budapest"),
        ("Helsinki", "Oslo"), ("Edinburgh", "Riga"), ("Tallinn", "Helsinki"),
        ("Geneva", "Porto"), ("Budapest", "Oslo"), ("Helsinki", "Geneva"),
        ("Riga", "Vilnius"), ("Tallinn", "Oslo")
    ]
    
    # Convert flights to a dictionary for easier access
    flight_dict = {}
    for src, dest in flights:
        if src not in flight_dict:
            flight_dict[src] = set()
        flight_dict[src].add(dest)
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Helper function to add a stay to the itinerary
    def add_stay(city, start_day, duration):
        end_day = start_day + duration - 1
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
        return end_day + 1
    
    # Backtracking function to find a valid itinerary
    def backtrack(city, current_day, visited):
        if len(visited) == len(constraints):
            # Check if the friend can be met in Oslo
            for stay in itinerary:
                if stay["place"] == "Oslo":
                    start_day, end_day = map(int, stay["day_range"].split('-')[0].split()[1:])
                    if constraints["Oslo"]["meet_friend"][0] <= start_day <= constraints["Oslo"]["meet_friend"][1]:
                        return True
            return False
        
        for next_city in flight_dict.get(city, []):
            if next_city not in visited:
                next_start_day = current_day
                if next_city == "Tallinn":
                    next_start_day = max(next_start_day, constraints[next_city]["wedding"][0])
                next_end_day = add_stay(next_city, next_start_day, constraints[next_city]["days"])
                visited.add(next_city)
                if backtrack(next_city, next_end_day, visited):
                    return True
                visited.remove(next_city)
                itinerary.pop()  # Remove the last added stay
        
        # Try staying in Oslo if not already visited and within the meet_friend window
        if city != "Oslo" and "Oslo" not in visited:
            for day in range(current_day, current_day + constraints["Oslo"]["days"] + 1):
                if constraints["Oslo"]["meet_friend"][0] <= day <= constraints["Oslo"]["meet_friend"][1]:
                    next_start_day = day
                    next_end_day = add_stay("Oslo", next_start_day, constraints["Oslo"]["days"])
                    visited.add("Oslo")
                    if backtrack("Oslo", next_end_day, visited):
                        return True
                    visited.remove("Oslo")
                    itinerary.pop()  # Remove the last added stay
        
        return False
    
    # Start from Porto
    visited = {"Porto"}
    current_day = add_stay("Porto", current_day, constraints["Porto"]["days"])
    if not backtrack("Porto", current_day, visited):
        raise ValueError("Cannot meet friend in Oslo within the given constraints.")
    
    return {"itinerary": itinerary}

# Output the itinerary as JSON
print(json.dumps(calculate_itinerary(), indent=4))