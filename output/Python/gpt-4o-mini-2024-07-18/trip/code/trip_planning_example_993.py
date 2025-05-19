import json

# Define the trip parameters
days_total = 15

# Cities and constraints
city_constraints = {
    'Riga': {'days': 2, 'position': None},
    'Frankfurt': {'days': 3, 'position': None},
    'Amsterdam': {'days': 2, 'friend_meeting': True},
    'Vilnius': {'days': 5, 'workshop': True},
    'London': {'days': 2, 'position': None},
    'Stockholm': {'days': 3, 'wedding': True},
    'Bucharest': {'days': 4, 'position': None}
}

# Define the direct flights
flights = {
    'London': ['Amsterdam', 'Bucharest', 'Frankfurt', 'Stockholm'],
    'Amsterdam': ['London', 'Stockholm', 'Frankfurt', 'Vilnius', 'Riga', 'Bucharest'],
    'Vilnius': ['Frankfurt', 'Riga', 'Amsterdam'],
    'Riga': ['Vilnius', 'Stockholm', 'Frankfurt', 'Amsterdam'],
    'Frankfurt': ['Vilnius', 'Stockholm', 'Riga', 'Amsterdam', 'London', 'Bucharest'],
    'Bucharest': ['London', 'Frankfurt', 'Amsterdam', 'Riga'],
    'Stockholm': ['Amsterdam', 'London', 'Frankfurt']
}

# Create an itinerary list
itinerary = []
day_counter = 1

# Define position of milestones
itinerary.append({'day_range': f'Day {day_counter}-{day_counter + city_constraints["Riga"]["days"] - 1}', 'place': 'Riga'})
day_counter += city_constraints["Riga"]["days"]

itinerary.append({'flying': f'Day {day_counter}-{day_counter}', 'from': 'Riga', 'to': 'Vilnius'})
itinerary.append({'day_range': f'Day {day_counter}-{day_counter + city_constraints["Vilnius"]["days"] - 1}', 'place': 'Vilnius'})
day_counter += city_constraints["Vilnius"]["days"]

# Schedule workshop within Vilnius days
itinerary.insert(-1, {'workshop': f'Day {day_counter - 2}-{day_counter - 1}'})  # assuming the workshop occupies day 7-11

itinerary.append({'flying': f'Day {day_counter}-{day_counter}', 'from': 'Vilnius', 'to': 'Frankfurt'})
itinerary.append({'day_range': f'Day {day_counter}-{day_counter + city_constraints["Frankfurt"]["days"] - 1}', 'place': 'Frankfurt'})
day_counter += city_constraints["Frankfurt"]["days"]

itinerary.append({'flying': f'Day {day_counter}-{day_counter}', 'from': 'Frankfurt', 'to': 'Amsterdam'})
itinerary.append({'day_range': f'Day {day_counter}-{day_counter + city_constraints["Amsterdam"]["days"] - 1}', 'place': 'Amsterdam'})
day_counter += city_constraints["Amsterdam"]["days"]

# Assume friend meeting happens after Day 2
itinerary.insert(-1, {'friend_meeting': f'Day {day_counter - 1}'})

itinerary.append({'flying': f'Day {day_counter}-{day_counter}', 'from': 'Amsterdam', 'to': 'London'})
itinerary.append({'day_range': f'Day {day_counter}-{day_counter + city_constraints["London"]["days"] - 1}', 'place': 'London'})
day_counter += city_constraints["London"]["days"]

itinerary.append({'flying': f'Day {day_counter}-{day_counter}', 'from': 'London', 'to': 'Stockholm'})
itinerary.append({'day_range': f'Day {day_counter}-{day_counter + city_constraints["Stockholm"]["days"] - 1}', 'place': 'Stockholm'})
day_counter += city_constraints["Stockholm"]["days"]

itinerary.append({'flying': f'Day {day_counter}-{day_counter}', 'from': 'Stockholm', 'to': 'Bucharest'})
itinerary.append({'day_range': f'Day {day_counter}-{day_counter + city_constraints["Bucharest"]["days"] - 1}', 'place': 'Bucharest'})
day_counter += city_constraints["Bucharest"]["days"]

# Function to convert into JSON structure
def itinerary_to_json(itinerary):
    plan = []
    for part in itinerary:
        if 'day_range' in part:
            plan.append(part)
        elif 'flying' in part:
            plan.append(part)
        elif 'friend_meeting' in part:
            plan.append(part)
        elif 'workshop' in part:
            plan.append(part)
    return json.dumps(plan, indent=4)

result_json = itinerary_to_json(itinerary)

# Output the result
print(result_json)