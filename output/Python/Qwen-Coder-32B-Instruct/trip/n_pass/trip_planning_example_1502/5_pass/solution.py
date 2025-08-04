from datetime import datetime, timedelta

# Sample data for demonstration purposes
start_date = datetime.strptime("2025-07-24", "%Y-%m-%d")
cities = ["CityA", "CityB", "CityC"]  # Example cities to cycle through

# Function to generate a 27-day itinerary
def generate_itinerary(start_date, cities, days=27):
    itinerary = []
    current_date = start_date
    num_cities = len(cities)
    
    for day in range(days):
        current_city = cities[day % num_cities]  # Cycle through the cities
        itinerary.append({"place": current_city, "date": current_date.strftime("%Y-%m-%d")})
        current_date += timedelta(days=1)  # Move to the next day
    
    return itinerary

# Generate the itinerary
itinerary = generate_itinerary(start_date, cities)

# Print the itinerary
for entry in itinerary:
    print(f"Date: {entry['date']}, Place: {entry['place']}")

# Find the next city after the last entry in the itinerary
def find_next_city(current_place, cities):
    # Assuming we cycle through the cities in the same order
    index = cities.index(current_place)
    next_city = cities[(index + 1) % len(cities)]
    return next_city

# Use the function to find the next city
next_city = find_next_city(itinerary[-1]["place"], cities)

print("\nNext City:", next_city)