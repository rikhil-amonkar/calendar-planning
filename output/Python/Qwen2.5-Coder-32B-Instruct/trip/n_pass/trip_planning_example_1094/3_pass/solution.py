# Example data for demonstration
direct_flights = {('CityA', 'CityB'), ('CityB', 'CityC')}
current_city = 'CityA'
city = 'CityB'

# Corrected if statement with an indented block
if (current_city, city) in direct_flights or (city, current_city) in direct_flights:
    # Code to execute if the condition is true
    print(f"There is a direct flight between {current_city} and {city}.")
else:
    # Optional: Code to execute if the condition is false
    print(f"There is no direct flight between {current_city} and {city}.")