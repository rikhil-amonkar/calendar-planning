import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Berlin": (3, [1, 3]),
        "Nice": (5, []),
        "Athens": (5, []),
        "Stockholm": (5, []),
        "Barcelona": (2, [3, 4]),
        "Vilnius": (4, []),
        "Lyon": (2, [4, 5])
    }
    
    # Define the direct flight connections
    flights = {
        "Lyon": ["Nice"],
        "Stockholm": ["Athens"],
        "Nice": ["Athens", "Berlin", "Barcelona"],
        "Berlin": ["Athens", "Nice", "Barcelona", "Vilnius", "Stockholm"],
        "Barcelona": ["Nice", "Athens", "Stockholm", "Lyon"],
        "Athens": ["Vilnius"],
        "Vilnius": [],
        "Lyon": []
    }
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    current_city = "Berlin"
    
    # Function to add a stay to the itinerary
    def add_stay(city, days, mandatory_days):
        nonlocal current_day
        itinerary.append({
            "day_range": f"Day {current_day}-{current_day + days - 1}",
            "place": city
        })
        current_day += days
    
    # Add Berlin stay
    add_stay("Berlin", 3, [1, 3])
    
    # Plan the rest of the itinerary
    while current_day <= 20:
        if current_city == "Berlin":
            if current_day == 4:
                next_city = "Nice"
            elif current_day == 7:
                next_city = "Barcelona"
        elif current_city == "Nice":
            if current_day == 12:
                next_city = "Athens"
        elif current_city == "Barcelona":
            if current_day == 9:
                next_city = "Lyon"
        elif current_city == "Lyon":
            if current_day == 11:
                next_city = "Vilnius"
        elif current_city == "Vilnius":
            if current_day == 15:
                next_city = "Stockholm"
        elif current_city == "Stockholm":
            if current_day == 20:
                break
        elif current_city == "Athens":
            if current_day == 17:
                next_city = "Stockholm"
        
        # Find a valid next city
        for city in flights[current_city]:
            if any(day >= current_day for day in constraints[city][1]) or current_day + constraints[city][0] <= 21:
                next_city = city
                break
        
        # Add the next city stay
        add_stay(next_city, constraints[next_city][0], constraints[next_city][1])
        current_city = next_city
    
    return {"itinerary": itinerary}

# Calculate and print the itinerary as JSON
print(json.dumps(calculate_itinerary(), indent=4))