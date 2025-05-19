import json

def compute_itinerary():
    # Input parameters
    days_in_vilnius = 4
    days_in_munich = 3
    days_in_mykonos = 7
    total_days = 12
    
    # Check the total days fit the requirements
    if days_in_vilnius + days_in_munich + days_in_mykonos != total_days:
        raise ValueError("Total days do not match the planned itinerary.")
    
    # Itinerary construction
    itinerary = []
    
    # Day allocation
    # Vilnius for 4 days
    itinerary.append({'day_range': 'Day 1-4', 'place': 'Vilnius'})
    
    # Flying from Vilnius to Munich (Day 4)
    itinerary.append({'flying': 'Day 4-4', 'from': 'Vilnius', 'to': 'Munich'})
    
    # Munich for 3 days
    itinerary.append({'day_range': 'Day 4-7', 'place': 'Munich'})
    
    # Flying from Munich to Mykonos (Day 7)
    itinerary.append({'flying': 'Day 7-7', 'from': 'Munich', 'to': 'Mykonos'})
    
    # Mykonos for 7 days
    itinerary.append({'day_range': 'Day 7-12', 'place': 'Mykonos'})
    
    # Output as JSON
    return json.dumps(itinerary, indent=4)

if __name__ == "__main__":
    result = compute_itinerary()
    print(result)