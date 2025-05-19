import json

def calculate_itinerary():
    # Input parameters
    total_days = 12
    days_in_vilnius = 4
    days_in_munich = 3
    days_in_mykonos = 7
    
    # Validate total days
    if days_in_vilnius + days_in_munich + days_in_mykonos != total_days:
        raise ValueError("Total days do not match the sum of days in each city.")
    
    # Flight connections
    flights = {
        'Vilnius': ['Munich'],
        'Munich': ['Vilnius', 'Mykonos'],
        'Mykonos': ['Munich']
    }
    
    # Determine the itinerary
    itinerary = []
    current_day = 1
    
    # Start in Vilnius (since it's only connected to Munich)
    itinerary.append({
        'day_range': f'Day {current_day}-{current_day + days_in_vilnius - 1}',
        'place': 'Vilnius'
    })
    current_day += days_in_vilnius
    
    # Fly from Vilnius to Munich
    itinerary.append({
        'flying': f'Day {current_day}-{current_day}',
        'from': 'Vilnius',
        'to': 'Munich'
    })
    
    # Stay in Munich
    itinerary.append({
        'day_range': f'Day {current_day + 1}-{current_day + days_in_munich}',
        'place': 'Munich'
    })
    current_day += days_in_munich + 1
    
    # Fly from Munich to Mykonos
    itinerary.append({
        'flying': f'Day {current_day}-{current_day}',
        'from': 'Munich',
        'to': 'Mykonos'
    })
    
    # Stay in Mykonos
    itinerary.append({
        'day_range': f'Day {current_day + 1}-{current_day + days_in_mykonos}',
        'place': 'Mykonos'
    })
    
    # Output the itinerary as JSON
    print(json.dumps(itinerary, indent=2))

if __name__ == "__main__":
    calculate_itinerary()