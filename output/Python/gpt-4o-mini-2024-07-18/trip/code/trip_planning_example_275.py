import json

def plan_trip():
    # Input constraints
    stay_in_split = 5
    stay_in_vilnius = 4
    stay_in_santorini = 2
    stay_in_madrid = 6
    total_days = 14

    # Plan
    itinerary = []
    
    # Vilnius
    itinerary.append({'day_range': 'Day 1-4', 'place': 'Vilnius'})
    
    # Travel from Vilnius to Split
    itinerary.append({'flying': 'Day 4-4', 'from': 'Vilnius', 'to': 'Split'})
    
    # Split
    itinerary.append({'day_range': 'Day 4-8', 'place': 'Split'})

    # Travel from Split to Madrid
    itinerary.append({'flying': 'Day 8-8', 'from': 'Split', 'to': 'Madrid'})
    
    # Madrid
    itinerary.append({'day_range': 'Day 8-13', 'place': 'Madrid'})
    
    # Travel from Madrid to Santorini
    itinerary.append({'flying': 'Day 13-13', 'from': 'Madrid', 'to': 'Santorini'})
    
    # Conference Days in Santorini
    itinerary.append({'day_range': 'Day 13-14', 'place': 'Santorini'})
    
    # Convert to JSON
    output_json = json.dumps(itinerary, indent=4)
    return output_json

if __name__ == "__main__":
    result = plan_trip()
    print(result)