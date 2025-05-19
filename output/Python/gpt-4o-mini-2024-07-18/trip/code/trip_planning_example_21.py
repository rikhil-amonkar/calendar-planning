import json

# Define trip parameters
total_days = 10
stay_venice = 6
stay_mykonos = 2
stay_vienna = 4
workshop_days = (5, 10)

# Compute the travel plan
itinerary = []

# Days in Venice and workshop constraints
itinerary.append({'day_range': f'Day 1-{stay_venice}', 'place': 'Venice'})
itinerary.append({'flying': f'Day {stay_venice}-{stay_venice}', 'from': 'Venice', 'to': 'Mykonos'})
itinerary.append({'day_range': f'Day {stay_venice + 1}-{stay_venice + stay_mykonos}', 'place': 'Mykonos'})
itinerary.append({'flying': f'Day {stay_venice + stay_mykonos}-{stay_venice + stay_mykonos}', 'from': 'Mykonos', 'to': 'Vienna'})
itinerary.append({'day_range': f'Day {stay_venice + stay_mykonos + 1}-{total_days}', 'place': 'Vienna'})

# Add workshop days and ensure it's within the Venice stay
if workshop_days[0] <= stay_venice <= workshop_days[1]:
    itinerary = [{
        'day_range': f'Day 1-{workshop_days[0] - 1}', 'place': 'Venice'
    }] + [{
        'flying': f'Day {workshop_days[0]}-{workshop_days[0]}', 'from': 'Venice', 'to': 'Mykonos'
    }] + [{
        'day_range': f'Day {workshop_days[0] + 1}-{workshop_days[1]}', 'place': 'Venice'
    }] + [{
        'flying': f'Day {workshop_days[1] + 1}-{workshop_days[1] + 1}', 'from': 'Venice', 'to': 'Vienna'
    }] + [{
        'day_range': f'Day {workshop_days[1] + 2}-{total_days}', 'place': 'Vienna'
    }]
    
# Output the itinerary as JSON
print(json.dumps(itinerary, indent=4))