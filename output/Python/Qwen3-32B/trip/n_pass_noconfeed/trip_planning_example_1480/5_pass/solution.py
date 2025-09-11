import json
from collections import defaultdict

# Define the cities and their required durations and constraints
cities = {
    'Geneva': {'required_days': 4, 'start_day': 1, 'end_day': 4},
    'Brussels': {'required_days': 2, 'start_day': 5, 'end_day': 6},
    'Venice': {'required_days': 5, 'start_day': 7, 'end_day': 11},
    'Vienna': {'required_days': 2},
    'Istanbul': {'required_days': 2},
    'Riga': {'required_days': 1},
    'Madrid': {'required_days': 1},
    'Vilnius': {'required_days': 4, 'start_day': 20, 'end_day': 23},
    'Munich': {'required_days': 3},
    'Reykjavik': {'required_days': 1},
    'Brussels_wedding': {'required_days': 2, 'start_day': 26, 'end_day': 27}
}

# Define direct flights as a bidirectional graph
direct_flights = [
    ('Munich', 'Vienna'), ('Istanbul', 'Brussels'), ('Vienna', 'Vilnius'), ('Madrid', 'Munich'),
    ('Venice', 'Brussels'), ('Riga', 'Brussels'), ('Geneva', 'Istanbul'), ('Munich', 'Reykjavik'),
    ('Vienna', 'Istanbul'), ('Riga', 'Istanbul'), ('Reykjavik', 'Vienna'), ('Venice', 'Munich'),
    ('Madrid', 'Venice'), ('Vilnius', 'Istanbul'), ('Venice', 'Vienna'), ('Venice', 'Istanbul'),
    ('Reykjavik', 'Madrid'), ('Riga', 'Munich'), ('Munich', 'Istanbul'), ('Reykjavik', 'Brussels'),
    ('Vilnius', 'Brussels'), ('Vilnius', 'Munich'), ('Madrid', 'Vienna'), ('Vienna', 'Brussels'),
    ('Geneva', 'Brussels'), ('Geneva', 'Madrid'), ('Munich', 'Brussels'), ('Madrid', 'Istanbul'),
    ('Geneva', 'Munich'), ('Riga', 'Vilnius'), ('Vilnius', 'Brussels_wedding'),  # Direct to Brussels_wedding
    ('Istanbul', 'Brussels_wedding')  # ✅ NEW DIRECT FLIGHT ADDED
]

# Build adjacency list
adj = defaultdict(list)
for a, b in direct_flights:
    adj[a].append(b)
    adj[b].append(a)

# Function to check if a city can be placed after the current sequence
def can_place(city, current_sequence, current_day):
    if city in current_sequence:
        return False
    if city in cities and 'start_day' in cities[city] and 'end_day' in cities[city]:
        required_start = cities[city]['start_day']
        required_end = cities[city]['end_day']
        city_start_day = current_day + 1
        city_end_day = city_start_day + cities[city]['required_days'] - 1
        if not (required_start <= city_start_day and city_end_day <= required_end):
            return False
    return True

# Backtracking to find a valid sequence
def backtrack(sequence, current_day, visited):
    if len(sequence) == len(cities):
        return sequence

    last_city = sequence[-1]
    for next_city in adj[last_city]:
        if next_city in visited:
            continue
        if not can_place(next_city, sequence, current_day):
            continue

        new_current_day = current_day + cities[next_city]['required_days']
        if new_current_day > 27:
            continue

        sequence.append(next_city)
        visited.add(next_city)
        result = backtrack(sequence, new_current_day, visited)
        if result is not None:
            return result
        sequence.pop()
        visited.remove(next_city)

    return None

# Start the sequence with Geneva, Brussels, Venice
initial_sequence = ['Geneva', 'Brussels', 'Venice']
visited = set(initial_sequence)
current_day = 11  # End of Venice

# Continue the backtracking
result_sequence = backtrack(initial_sequence, current_day, visited)

# Generate the itinerary from the result sequence
def generate_itinerary(sequence):
    itinerary = []
    prev_end = 0
    for city in sequence:
        if city in cities and 'start_day' in cities[city] and 'end_day' in cities[city]:
            start = cities[city]['start_day']
            end = cities[city]['end_day']
        else:
            start = prev_end + 1
            duration = cities[city]['required_days']
            end = start + duration - 1
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
        prev_end = end
    return itinerary

# Output the JSON
if result_sequence:
    itinerary = generate_itinerary(result_sequence)
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print(json.dumps({"error": "No valid itinerary found"}, indent=2))