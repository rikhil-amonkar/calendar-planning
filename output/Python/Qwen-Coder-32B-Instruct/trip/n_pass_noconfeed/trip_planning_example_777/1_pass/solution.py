import json

def calculate_itinerary():
    # Define the constraints
    total_days = 15
    days_in_dublin = 5
    days_in_helsinki = 3
    helsinki_meeting_days = (3, 5)
    days_in_riga = 3
    days_in_reykjavik = 2
    days_in_vienna = 2
    vienna_show_days = (2, 3)
    days_in_tallinn = 5
    tallinn_wedding_days = (7, 11)
    
    # Define the direct flight connections
    flights = {
        'Helsinki': ['Riga', 'Dublin', 'Vienna', 'Tallinn', 'Reykjavik'],
        'Riga': ['Helsinki', 'Tallinn', 'Dublin', 'Vienna'],
        'Dublin': ['Helsinki', 'Riga', 'Tallinn', 'Reykjavik'],
        'Tallinn': ['Riga', 'Helsinki', 'Dublin'],
        'Vienna': ['Helsinki', 'Riga', 'Reykjavik', 'Dublin'],
        'Reykjavik': ['Helsinki', 'Dublin', 'Vienna']
    }
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Start in Dublin for 5 days
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_dublin - 1}", "place": "Dublin"})
    current_day += days_in_dublin
    
    # Move to Vienna for 2 days to attend the show
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_vienna - 1}", "place": "Vienna"})
    current_day += days_in_vienna
    
    # Move to Helsinki for 3 days to meet friends
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_helsinki - 1}", "place": "Helsinki"})
    current_day += days_in_helsinki
    
    # Move to Riga for 3 days
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_riga - 1}", "place": "Riga"})
    current_day += days_in_riga
    
    # Move to Tallinn for 5 days to attend the wedding
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_tallinn - 1}", "place": "Tallinn"})
    current_day += days_in_tallinn
    
    # Move to Reykjavik for 2 days
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_reykjavik - 1}", "place": "Reykjavik"})
    current_day += days_in_reykjavik
    
    return {"itinerary": itinerary}

# Calculate and print the itinerary
print(json.dumps(calculate_itinerary()))