import json

def compute_itinerary():
    # Define the constraints and parameters
    total_days = 17
    days_in_riga = 7
    days_in_budapest = 7
    days_in_paris = 4
    days_in_warsaw = 2
    
    wedding_start = 11
    wedding_end = 17
    
    # Initialize itinerary
    itinerary = []
    
    # Step 1: Plan days for Warsaw (show)
    itinerary.append({'day_range': 'Day 1-2', 'place': 'Warsaw'})
    
    # Step 2: Travel to Riga
    # From Day 3 to Day 9 in Riga
    itinerary.append({'flying': 'Day 2-3', 'from': 'Warsaw', 'to': 'Riga'})
    itinerary.append({'day_range': 'Day 3-9', 'place': 'Riga'})
    
    # Step 3: Attend wedding in Riga
    # Wedding days are within days 11-17, so stay in Riga until day 9 (2 extra days for wedding)
    # Move back to Budapest after wedding
    itinerary.append({'flying': 'Day 9-10', 'from': 'Riga', 'to': 'Budapest'})
    
    # Step 4: Days in Budapest
    itinerary.append({'day_range': 'Day 10-16', 'place': 'Budapest'})
    
    # Step 5: Return to Paris and allocate days there
    itinerary.append({'flying': 'Day 16-17', 'from': 'Budapest', 'to': 'Paris'})
    itinerary.append({'day_range': 'Day 17-17', 'place': 'Paris'})
    
    # Collect days based on constraints
    # Adjusting the days in Paris
    itinerary.insert(4, {'day_range': 'Day 16-17', 'place': 'Paris'})  # add Paris here to the existing
    
    # Output results in JSON format
    return json.dumps(itinerary, indent=4)

# Execute function and print the itinerary
itinerary_json = compute_itinerary()
print(itinerary_json)