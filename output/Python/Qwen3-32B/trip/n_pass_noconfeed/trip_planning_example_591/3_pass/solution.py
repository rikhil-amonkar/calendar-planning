# Define the starting days for each city
start_days = {
    'Paris': 10,
    'Rome': 15,
    'Berlin': 20
}

# List of cities to iterate over
cities = ['Paris', 'Rome', 'Berlin']

# Process each city
for city in cities:
    current_end = start_days[city] - 1
    print(f"End day for {city}: {current_end}")