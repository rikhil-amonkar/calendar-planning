import json

def compute_itinerary():
    itinerary = []
    
    # Total days for each segment
    days_in_lisbon = 2
    days_in_dubrovnik = 5
    days_in_copenhagen = 5
    days_in_prague = 3
    days_in_tallinn = 2
    days_in_stockholm = 4
    days_in_split = 3
    days_in_lyon = 2

    # Workshop in Lisbon (between day 4 and day 5)
    workshop_days = (4, 5)

    # Meeting a friend in Tallinn (between day 1 and day 2)
    friend_meeting_days = (1, 2)

    # Wedding in Stockholm (between day 13 and day 16)
    wedding_days = (13, 16)

    # Annual show in Lyon (day 18 to day 19)
    annual_show_days = (18, 19)
    
    # Define the trip
    # Day 1-2: Tallinn (meet friend)
    itinerary.append({'day_range': 'Day 1-2', 'place': 'Tallinn'})
    
    # Day 3: Fly from Tallinn to Lisbon
    itinerary.append({'flying': 'Day 3-3', 'from': 'Tallinn', 'to': 'Lisbon'})
    
    # Day 3-4: Lisbon
    itinerary.append({'day_range': 'Day 3-4', 'place': 'Lisbon'})
    
    # Day 4: Workshop day in Lisbon (day 4)
    itinerary.append({'day_range': 'Day 4-4', 'place': 'Lisbon (Workshop)'})
    
    # Day 5: Lisbon to Dubrovnik (after workshop, no overlap)
    itinerary.append({'flying': 'Day 5-5', 'from': 'Lisbon', 'to': 'Dubrovnik'})
    
    # Day 5-9: Dubrovnik
    itinerary.append({'day_range': 'Day 5-9', 'place': 'Dubrovnik'})
    
    # Day 10: Dubrovnik to Copenhagen
    itinerary.append({'flying': 'Day 10-10', 'from': 'Dubrovnik', 'to': 'Copenhagen'})
    
    # Day 10-14: Copenhagen
    itinerary.append({'day_range': 'Day 10-14', 'place': 'Copenhagen'})
    
    # Day 15: Copenhagen to Stockholm
    itinerary.append({'flying': 'Day 15-15', 'from': 'Copenhagen', 'to': 'Stockholm'})
    
    # Day 15-18: Stockholm (includes wedding)
    itinerary.append({'day_range': 'Day 15-18', 'place': 'Stockholm'})
    
    # Day 18: Stockholm to Lyon (before annual show)
    itinerary.append({'flying': 'Day 18-18', 'from': 'Stockholm', 'to': 'Lyon'})
    
    # Day 18-19: Lyon (annual show)
    itinerary.append({'day_range': 'Day 18-19', 'place': 'Lyon (Annual Show)'})
    
    # We still need to cover Prague and Split
    # Day 14: Copenhagen to Prague (after staying in Copenhagen)
    itinerary.append({'flying': 'Day 14-14', 'from': 'Copenhagen', 'to': 'Prague'})
    
    # Day 14-16: Prague
    itinerary.append({'day_range': 'Day 14-16', 'place': 'Prague'})
    
    # Day 16: Prague to Split
    itinerary.append({'flying': 'Day 16-16', 'from': 'Prague', 'to': 'Split'})
    
    # Day 16-18: Split
    itinerary.append({'day_range': 'Day 16-18', 'place': 'Split'})
    
    # Format output as JSON
    return json.dumps(itinerary, indent=4)

# Calculate and print the itinerary
if __name__ == "__main__":
    trip_itinerary = compute_itinerary()
    print(trip_itinerary)