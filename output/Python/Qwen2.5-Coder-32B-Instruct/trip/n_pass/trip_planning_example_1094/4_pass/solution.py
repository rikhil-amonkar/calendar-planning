# Example data for demonstration
cities = ['CityA', 'CityB', 'CityC', 'CityD', 'CityE']
flights = {
    ('CityA', 'CityB'): 2,  # Flight from CityA to CityB takes 2 days
    ('CityB', 'CityC'): 3,  # Flight from CityB to CityC takes 3 days
    ('CityC', 'CityD'): 4,  # Flight from CityC to CityD takes 4 days
    ('CityD', 'CityE'): 2,  # Flight from CityD to CityE takes 2 days
    ('CityE', 'CityA'): 5   # Flight from CityE to CityA takes 5 days
}

# Starting city
current_city = 'CityA'

# Initialize the itinerary
itinerary = [current_city]
total_days = 0

# Construct the itinerary
while total_days < 16:
    next_city = None
    for (start, end), days in flights.items():
        if start == current_city and (next_city is None or days < flights[(next_city, itinerary[-2])]):
            next_city = end
            days_to_next_city = days
    
    # Add the next city to the itinerary
    itinerary.append(next_city)
    total_days += days_to_next_city
    current_city = next_city

    # If we've completed a full cycle and still need more days, reset to the start
    if total_days >= 16:
        break
    elif len(itinerary) > len(cities) * 2:  # Avoid infinite loops
        raise ValueError("Unable to construct a valid itinerary within 16 days.")

# Print the itinerary and total days
print("Itinerary:", " -> ".join(itinerary))
print("Total Days:", total_days)