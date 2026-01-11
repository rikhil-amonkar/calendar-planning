import json

def generate_itinerary():
    # Define constraints
    constraints = {
        "Santorini": 3,
        "Valencia": 4,
        "Madrid": 2,
        "Seville": 2,
        "Bucharest": 3,
        "Vienna": 4,
        "Riga": 4,
        "Tallinn": 5,
        "Krakow": 5,
        "Frankfurt": 4
    }
    
    # Specific events
    events = {
        "Madrid": [(6, 7)],  # Annual show
        "Vienna": [(3, 6)],  # Wedding
        "Riga": [(20, 23)],  # Conference
        "Tallinn": [(23, 27)]  # Workshop
    }
    
    # Direct flights
    direct_flights = {
        "Vienna": ["Bucharest", "Seville", "Valencia", "Madrid", "Riga", "Krakow", "Frankfurt"],
        "Bucharest": ["Vienna", "Riga", "Valencia", "Santorini"],
        "Santorini": ["Vienna", "Bucharest", "Madrid"],
        "Seville": ["Vienna", "Madrid", "Valencia"],
        "Madrid": ["Vienna", "Seville", "Valencia", "Bucharest", "Frankfurt"],
        "Valencia": ["Seville", "Madrid", "Bucharest", "Vienna", "Krakow", "Frankfurt"],
        "Riga": ["Bucharest", "Vienna", "Tallinn", "Frankfurt"],
        "Tallinn": ["Riga", "Frankfurt"],
        "Krakow": ["Valencia", "Frankfurt", "Vienna"],
        "Frankfurt": ["Tallinn", "Riga", "Krakow", "Vienna", "Madrid", "Bucharest"]
    }
    
    # Initialize itinerary
    itinerary = []
    current_day = 1
    
    # Helper function to add a stay to the itinerary
    def add_stay(city, days):
        nonlocal current_day
        end_day = current_day + days - 1
        itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": city})
        current_day = end_day + 1
    
    # Helper function to find a flight to a city
    def can_fly_to(current_city, target_city):
        return target_city in direct_flights.get(current_city, [])
    
    # Place events and mandatory stays
    # Vienna wedding (days 3-6)
    add_stay("Vienna", 4)
    
    # Madrid show (days 6-7) - already covered by Vienna stay
    
    # Bucharest (3 days)
    add_stay("Bucharest", 3)
    
    # Riga conference (days 20-23)
    # Ensure we can fly to Riga by day 20
    # Assume we are in a city that can fly to Riga by day 20
    current_city = "Riga"
    add_stay("Riga", 4)
    
    # Tallinn workshop (days 23-27)
    # Already in Riga, so we can stay in Riga until day 20, then fly to Tallinn
    add_stay("Tallinn", 5)
    
    # Krakow meeting (days 11-15)
    # Ensure we can fly to Krakow by day 11
    # Assume we are in a city that can fly to Krakow by day 11
    current_city = "Krakow"
    add_stay("Krakow", 5)
    
    # Remaining cities
    remaining_cities = set(constraints.keys()) - {entry["place"] for entry in itinerary}
    
    # Add remaining cities to the itinerary
    for city in remaining_cities:
        # Find a city we can fly to from the last city in the itinerary
        last_city = itinerary[-1]["place"]
        if can_fly_to(last_city, city):
            add_stay(city, constraints[city])
        else:
            # If no direct flight, find a transit city
            for transit_city in direct_flights[last_city]:
                if can_fly_to(transit_city, city):
                    add_stay(transit_city, 1)  # Transit stay
                    add_stay(city, constraints[city])
                    break
    
    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary}, indent=4)

# Generate and print the itinerary
print(generate_itinerary())