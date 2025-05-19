import json

def calculate_itinerary():
    # Define the required stays and events
    city_durations = {
        'Madrid': 4,
        'Dublin': 3,
        'Tallinn': 2
    }
    
    events = {
        'Tallinn': (6, 7)
    }
    
    # Define direct flight connections
    flight_connections = {
        'Madrid': ['Dublin'],
        'Dublin': ['Madrid', 'Tallinn'],
        'Tallinn': ['Dublin']
    }
    
    # Determine the order of cities based on constraints
    itinerary = []
    current_day = 1
    
    # Start with Madrid
    madrid_days = city_durations['Madrid']
    itinerary.append({'day_range': f'Day {current_day}-{current_day + madrid_days - 1}', 'place': 'Madrid'})
    current_day += madrid_days
    
    # Fly to Dublin
    itinerary.append({'flying': f'Day {current_day - 1}-{current_day - 1}', 'from': 'Madrid', 'to': 'Dublin'})
    
    # Stay in Dublin
    dublin_days = city_durations['Dublin']
    itinerary.append({'day_range': f'Day {current_day - 1}-{current_day - 1 + dublin_days - 1}', 'place': 'Dublin'})
    current_day += dublin_days
    
    # Fly to Tallinn for the workshop
    itinerary.append({'flying': f'Day {current_day - 1}-{current_day - 1}', 'from': 'Dublin', 'to': 'Tallinn'})
    
    # Stay in Tallinn
    tallinn_days = city_durations['Tallinn']
    itinerary.append({'day_range': f'Day {current_day - 1}-{current_day - 1 + tallinn_days - 1}', 'place': 'Tallinn'})
    
    return itinerary

itinerary = calculate_itinerary()
print(json.dumps(itinerary, indent=2))