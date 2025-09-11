# Define the cities and their constraints
cities = {
    "Paris": {
        "constraints": ["No night flights", "Max 3 days in city"]
    },
    "Tokyo": {
        "constraints": ["Visa required", "Language barrier"]
    },
    "New York": {
        "constraints": ["High accommodation costs", "Weekend only"]
    }
}

# Iterate over each city and its constraints
for city in cities:
    print(f"Constraints for {city}:")
    for constraint in cities[city]["constraints"]:
        print(f" - {constraint}")