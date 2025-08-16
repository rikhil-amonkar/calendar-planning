import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Paris": (5, 4, 8),
        "Warsaw": (2, None, None),
        "Krakow": (2, 17, 18),
        "Tallinn": (2, None, None),
        "Riga": (2, 23, 24),
        "Copenhagen": (5, None, None),
        "Helsinki": (5, 18, 22),
        "Oslo": (5, None, None),
        "Santorini": (2, 12, 13),
        "Lyon": (4, None, None)
    }
    
    # Define the flight connections
    flights = {
        "Warsaw": ["Riga", "Tallinn", "Copenhagen", "Krakow"],
        "Riga": ["Warsaw", "Tallinn", "Oslo", "Helsinki", "Copenhagen", "Paris"],
        "Tallinn": ["Warsaw", "Riga", "Oslo", "Helsinki"],
        "Copenhagen": ["Helsinki", "Warsaw", "Lyon", "Oslo", "Krakow", "Riga", "Santorini", "Paris"],
        "Helsinki": ["Tallinn", "Riga", "Copenhagen", "Krakow", "Oslo", "Paris"],
        "Oslo": ["Tallinn", "Helsinki", "Copenhagen", "Lyon", "Paris", "Krakow", "Santorini", "Riga"],
        "Lyon": ["Paris", "Copenhagen", "Oslo"],
        "Paris": ["Lyon", "Oslo", "Riga", "Tallinn", "Helsinki", "Copenhagen", "Krakow", "Warsaw"],
        "Krakow": ["Helsinki", "Warsaw", "Oslo", "Copenhagen", "Paris"],
        "Santorini": ["Copenhagen", "Oslo"]
    }
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    current_city = "Paris"
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints[current_city][0] - 1}", "place": current_city})
    current_day += constraints[current_city][0]
    
    # Plan the rest of the itinerary
    def find_next_city(current_city, current_day):
        for city, (days, start, end) in constraints.items():
            if city != current_city and city not in [i['place'] for i in itinerary]:
                if start is None or (start <= current_day <= end or start <= current_day + days - 1 <= end):
                    if any(flight == city for flight in flights[current_city]):
                        return city
        return None
    
    while current_day < 25:
        next_city = find_next_city(current_city, current_day)
        if next_city:
            days = constraints[next_city][0]
            itinerary.append({"day_range": f"Day {current_day}-{current_day + days - 1}", "place": next_city})
            current_day += days
            current_city = next_city
        else:
            break
    
    return itinerary

# Calculate and output the itinerary
itinerary = calculate_itinerary()
output = {"itinerary": itinerary}
print(json.dumps(output))