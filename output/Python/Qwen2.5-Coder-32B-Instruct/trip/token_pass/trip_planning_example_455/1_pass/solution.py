import json

def generate_itinerary():
    # Define the constraints
    constraints = {
        "Reykjavik": 7,
        "Riga": 2,
        "Warsaw": 3,
        "Istanbul": 6,
        "Krakow": 7
    }
    
    # Define the flight connections
    flights = {
        "Istanbul": ["Krakow", "Warsaw"],
        "Warsaw": ["Reykjavik", "Istanbul", "Krakow", "Riga"],
        "Riga": ["Istanbul", "Warsaw"],
        "Krakow": ["Istanbul", "Warsaw"]
    }
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Start in Riga to meet the friend between day 1 and day 2
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Riga'] - 1}", "place": "Riga"})
    current_day += constraints['Riga']
    
    # From Riga, fly to Warsaw (since we need to attend the wedding in Istanbul)
    itinerary.append({"day_range": f"Day {current_day}-{current_day}", "place": "Warsaw"})
    current_day += 1
    
    # Stay in Warsaw for 2 more days
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Warsaw'] - 2}", "place": "Warsaw"})
    current_day += constraints['Warsaw'] - 1
    
    # From Warsaw, fly to Istanbul to attend the wedding
    itinerary.append({"day_range": f"Day {current_day}-{current_day}", "place": "Istanbul"})
    current_day += 1
    
    # Stay in Istanbul for 5 more days (total 6 days in Istanbul)
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Istanbul'] - 2}", "place": "Istanbul"})
    current_day += constraints['Istanbul'] - 1
    
    # From Istanbul, fly to Krakow
    itinerary.append({"day_range": f"Day {current_day}-{current_day}", "place": "Krakow"})
    current_day += 1
    
    # Stay in Krakow for the remaining days
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Krakow'] - 2}", "place": "Krakow"})
    current_day += constraints['Krakow'] - 1
    
    # Finally, fly to Reykjavik
    itinerary.append({"day_range": f"Day {current_day}-{current_day}", "place": "Reykjavik"})
    current_day += 1
    
    # Stay in Reykjavik for the remaining days
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Reykjavik'] - 2}", "place": "Reykjavik"})
    current_day += constraints['Reykjavik'] - 1
    
    return {"itinerary": itinerary}

# Generate and print the itinerary as JSON
itinerary_json = generate_itinerary()
print(json.dumps(itinerary_json, indent=4))