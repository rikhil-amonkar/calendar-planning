import json

def generate_itinerary():
    # Define the constraints
    city_days = {
        "Brussels": 3,
        "Helsinki": 3,
        "Split": 4,
        "Dubrovnik": 2,
        "Istanbul": 5,
        "Milan": 4,
        "Vilnius": 5,
        "Frankfurt": 3
    }
    
    # Define events
    events = {
        "Istanbul": (1, 5),  # Annual show
        "Vilnius": (18, 22),  # Workshop
        "Frankfurt": (16, 18)  # Wedding
    }
    
    # Direct flights
    direct_flights = [
        ("Milan", "Frankfurt"), ("Split", "Frankfurt"), ("Milan", "Split"),
        ("Brussels", "Vilnius"), ("Brussels", "Helsinki"), ("Istanbul", "Brussels"),
        ("Milan", "Vilnius"), ("Brussels", "Milan"), ("Istanbul", "Helsinki"),
        ("Helsinki", "Vilnius"), ("Helsinki", "Dubrovnik"), ("Split", "Vilnius"),
        ("Dubrovnik", "Istanbul"), ("Istanbul", "Milan"), ("Helsinki", "Frankfurt"),
        ("Istanbul", "Vilnius"), ("Split", "Helsinki"), ("Milan", "Helsinki"),
        ("Istanbul", "Frankfurt"), ("Brussels", "Frankfurt"), ("Dubrovnik", "Frankfurt"),
        ("Frankfurt", "Vilnius")
    ]
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Place cities with fixed events first
    def add_to_itinerary(city, start_day, end_day):
        nonlocal current_day
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
        current_day = end_day + 1
    
    # Add Istanbul first due to the annual show
    add_to_itinerary("Istanbul", 1, 5)
    
    # Add Frankfurt next due to the wedding
    add_to_itinerary("Frankfurt", 16, 18)
    
    # Add Vilnius last due to the workshop
    add_to_itinerary("Vilnius", 18, 22)
    
    # Remaining cities: Brussels, Helsinki, Split, Dubrovnik, Milan
    remaining_cities = ["Brussels", "Helsinki", "Split", "Dubrovnik", "Milan"]
    
    # Function to check if a direct flight exists between two cities
    def has_direct_flight(city1, city2):
        return (city1, city2) in direct_flights or (city2, city1) in direct_flights
    
    # Helper function to find the next possible city to visit
    def find_next_city(current_city, remaining_cities):
        for city in remaining_cities:
            if has_direct_flight(current_city, city):
                return city
        return None
    
    # Start from the last city added (Vilnius) and work backwards
    current_city = "Vilnius"
    while remaining_cities:
        next_city = find_next_city(current_city, remaining_cities)
        if next_city:
            days = city_days[next_city]
            add_to_itinerary(next_city, current_day, current_day + days - 1)
            remaining_cities.remove(next_city)
            current_city = next_city
        else:
            # If no direct flight found, try to connect through another city
            for city in remaining_cities:
                for connecting_city in [c for c in remaining_cities if c != city]:
                    if has_direct_flight(current_city, connecting_city) and has_direct_flight(connecting_city, city):
                        days = city_days[connecting_city]
                        add_to_itinerary(connecting_city, current_day, current_day + days - 1)
                        current_day += days
                        days = city_days[city]
                        add_to_itinerary(city, current_day, current_day + days - 1)
                        remaining_cities.remove(connecting_city)
                        remaining_cities.remove(city)
                        current_city = city
                        break
                if not remaining_cities:
                    break
    
    # Return the itinerary as a JSON-formatted dictionary
    return json.dumps({"itinerary": itinerary}, indent=4)

# Generate and print the itinerary
print(generate_itinerary())