import json

def compute_itinerary():
    # Trip constraints
    total_days = 12
    stay_riga = 5
    stay_vilnius = 7
    stay_dublin = 2

    # Starting from Riga
    itinerary = []
    
    # Day range for Riga
    itinerary.append({'day_range': 'Day 1-5', 'place': 'Riga'})
    
    # Travel day to Vilnius (Day 5)
    itinerary.append({'flying': 'Day 5-5', 'from': 'Riga', 'to': 'Vilnius'})
    
    # Day range for Vilnius
    itinerary.append({'day_range': 'Day 5-12', 'place': 'Vilnius'})
    
    # Travel day to Dublin (Day 12)
    itinerary.append({'flying': 'Day 12-12', 'from': 'Vilnius', 'to': 'Dublin'})
    
    # Day range for Dublin
    itinerary.append({'day_range': 'Day 12-12', 'place': 'Dublin'})
    
    return itinerary

if __name__ == '__main__':
    trip_plan = compute_itinerary()
    print(json.dumps(trip_plan, indent=4))