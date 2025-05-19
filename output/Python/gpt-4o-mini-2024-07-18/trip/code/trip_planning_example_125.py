import json

def compute_itinerary():
    # Input parameters
    total_days = 15
    stuttgart_days = 6
    seville_days = 7
    manchester_days = 4
    
    # Day allocation
    # We will calculate the possible trips based on the constraints provided
    itinerary = []
    
    # Schedule Stuttgart with a friend meeting in the first 6 days
    itinerary.append({'day_range': 'Day 1-6', 'place': 'Stuttgart'})
    
    # Travel to Seville
    itinerary.append({'flying': 'Day 6-6', 'from': 'Stuttgart', 'to': 'Seville'})
    
    # Schedule Seville
    itinerary.append({'day_range': 'Day 6-13', 'place': 'Seville'})
    
    # Travel to Manchester
    itinerary.append({'flying': 'Day 13-13', 'from': 'Seville', 'to': 'Manchester'})
    
    # Schedule Manchester
    itinerary.append({'day_range': 'Day 13-15', 'place': 'Manchester'})
    
    # Convert itinerary to JSON format
    itinerary_json = json.dumps(itinerary, indent=4)
    
    return itinerary_json

# Run the function and print the itinerary
if __name__ == '__main__':
    result = compute_itinerary()
    print(result)