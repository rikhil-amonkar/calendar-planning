import json

def plan_trip(total_days, city_durations, event_constraints, direct_flights):
    cities = list(city_durations.keys())
    itinerary = []
    current_day = 1
    
    # Find the city with event constraint that must be visited first
    first_city = None
    for city, duration in city_durations.items():
        if city in event_constraints:
            start_day, end_day = event_constraints[city]
            if start_day == 1:
                first_city = city
                break
    
    if not first_city:
        # No event constraint starting on day 1, choose any city
        first_city = cities[0]
    
    remaining_cities = [city for city in cities if city != first_city]
    
    # Visit first city
    duration = city_durations[first_city]
    end_day = current_day + duration - 1
    itinerary.append({'day_range': f'Day {current_day}-{end_day}', 'place': first_city})
    current_day = end_day + 1
    
    # Determine next city based on direct flights
    next_city = None
    for city in remaining_cities:
        if (first_city, city) in direct_flights or (city, first_city) in direct_flights:
            next_city = city
            break
    
    if next_city:
        remaining_cities.remove(next_city)
        # Fly to next city
        itinerary.append({'flying': f'Day {current_day-1}-{current_day-1}', 'from': first_city, 'to': next_city})
        
        # Visit next city
        duration = city_durations[next_city]
        end_day = current_day + duration - 1
        itinerary.append({'day_range': f'Day {current_day}-{end_day}', 'place': next_city})
        current_day = end_day + 1
        
        # Check if there's a third city
        if remaining_cities:
            third_city = remaining_cities[0]
            # Verify if there's a direct flight from next_city to third_city
            if (next_city, third_city) in direct_flights or (third_city, next_city) in direct_flights:
                # Fly to third city
                itinerary.append({'flying': f'Day {current_day-1}-{current_day-1}', 'from': next_city, 'to': third_city})
                
                # Visit third city
                duration = city_durations[third_city]
                end_day = current_day + duration - 1
                itinerary.append({'day_range': f'Day {current_day}-{end_day}', 'place': third_city})
    
    return itinerary

# Example usage (commented out for the actual submission)
# total_days = 14
# city_durations = {
#     'Santorini': 6,
#     'Krakow': 5,
#     'London': 5
# }
# event_constraints = {
#     'Santorini': (1, 6)
# }
# direct_flights = {('London', 'Krakow'), ('Santorini', 'London')}
# itinerary = plan_trip(total_days, city_durations, event_constraints, direct_flights)
# print(json.dumps(itinerary, indent=2))

# Main execution
if __name__ == "__main__":
    # Input parameters for the given task
    total_days = 14
    city_durations = {
        'Santorini': 6,
        'Krakow': 5,
        'London': 5
    }
    event_constraints = {
        'Santorini': (1, 6)
    }
    direct_flights = {('London', 'Krakow'), ('Santorini', 'London')}
    
    itinerary = plan_trip(total_days, city_durations, event_constraints, direct_flights)
    print(json.dumps(itinerary))