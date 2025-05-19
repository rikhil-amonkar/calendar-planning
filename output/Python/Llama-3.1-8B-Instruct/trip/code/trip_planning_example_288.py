import json

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Stuttgart': 5,
            'Manchester': 7,
            'Madrid': 4,
            'Vienna': 2
        }
        self.flights = {
            ('Vienna', 'Stuttgart'): 1,
            ('Manchester', 'Vienna'): 1,
            ('Madrid', 'Vienna'): 1,
            ('Manchester', 'Stuttgart'): 1,
            ('Manchester', 'Madrid'): 1
        }

    def generate_itinerary(self, days, constraints):
        # Sort cities by duration in descending order
        sorted_cities = sorted(constraints, key=lambda x: self.cities[x], reverse=True)

        # Initialize the optimal itinerary
        optimal_itinerary = []

        # Iterate over cities to find the optimal itinerary
        for i, city in enumerate(sorted_cities):
            days_in_city = self.cities[city]
            if i == 0:
                days_left = days - days_in_city
                optimal_itinerary.append({'day_range': f'Day 1-{days_in_city}', 'place': city})
            else:
                if (sorted_cities[i-1], city) in self.flights:
                    days_left -= 1
                    optimal_itinerary.append({'flying': f'Day {days_left+1}-{days_left+1}', 'from': sorted_cities[i-1], 'to': city})
                days_left -= days_in_city
                optimal_itinerary.append({'day_range': f'Day {days_left+1}-{days_left+days_in_city}', 'place': city})

        # Add wedding and workshop constraints
        for i, item in enumerate(optimal_itinerary):
            if 'Manchester' in item['place'] and days_in_city == 7:
                optimal_itinerary[i]['day_range'] = f'Day 1-{days}'
            if 'Stuttgart' in item['place'] and days_in_city == 5:
                optimal_itinerary[i]['day_range'] = f'Day 11-{days}'

        return optimal_itinerary

    def plan_trip(self):
        constraints = ['Stuttgart', 'Manchester', 'Madrid', 'Vienna']
        days = 15
        itinerary = self.generate_itinerary(days, constraints)
        return json.dumps(itinerary, indent=4)

if __name__ == '__main__':
    trip_planner = TripPlanner()
    print(trip_planner.plan_trip())