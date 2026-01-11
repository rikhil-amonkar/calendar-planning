import json

def generate_itinerary():
    # Define the constraints
    days_in_madrid = 4
    days_in_dublin = 3
    days_in_tallinn = 2
    workshop_days_in_tallinn = [6, 7]
    
    # Initialize the itinerary list
    itinerary = []
    
    # Start in Madrid for 4 days
    itinerary.append({"day_range": f"Day 1-{days_in_madrid}", "place": "Madrid"})
    
    # Transition to Dublin after Madrid
    start_day_in_dublin = days_in_madrid + 1
    end_day_in_dublin = start_day_in_dublin + days_in_dublin - 1
    itinerary.append({"day_range": f"Day {start_day_in_dublin}-{end_day_in_dublin}", "place": "Dublin"})
    
    # Transition to Tallinn after Dublin, ensuring the workshop day constraint
    start_day_in_tallinn = max(workshop_days_in_tallinn) - days_in_tallinn + 1
    end_day_in_tallinn = start_day_in_tallinn + days_in_tallinn - 1
    itinerary.append({"day_range": f"Day {start_day_in_tallinn}-{end_day_in_tallinn}", "place": "Tallinn"})
    
    # Return the itinerary as a JSON-formatted dictionary
    return {"itinerary": itinerary}

# Generate and print the itinerary
itinerary_json = generate_itinerary()
print(json.dumps(itinerary_json, indent=4))