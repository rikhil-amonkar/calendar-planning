import json

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Porto': 5,
            'Prague': 4,
            'Reykjavik': 4,
            'Santorini': 2,
            'Amsterdam': 2,
            'Munich': 4
        }
        self.flights = {
            ('Porto', 'Amsterdam'): 1,
            ('Munich', 'Amsterdam'): 1,
            ('Reykjavik', 'Amsterdam'): 1,
            ('Munich', 'Porto'): 1,
            ('Prague', 'Reykjavik'): 1,
            ('Reykjavik', 'Munich'): 1,
            ('Amsterdam', 'Santorini'): 1,
            ('Prague', 'Amsterdam'): 1,
            ('Prague', 'Munich'): 1
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

        # Add wedding and conference constraints
        for i, item in enumerate(optimal_itinerary):
            if 'Reykjavik' in item['place'] and days_in_city == 4 and 4 <= days_left + days_in_city <= 7:
                optimal_itinerary[i]['day_range'] = f'Day {days_left+1}-{days}'
            if 'Amsterdam' in item['place'] and days_in_city == 2 and 14 <= days_left + days_in_city <= 15:
                optimal_itinerary[i]['day_range'] = f'Day {days_left+1}-{days}'

        # Add meeting constraint
        for i, item in enumerate(optimal_itinerary):
            if 'Munich' in item['place'] and days_in_city == 4 and 7 <= days_left + days_in_city <= 10:
                optimal_itinerary[i]['day_range'] = f'Day {days_left+1}-{days}'

        return optimal_itinerary

    def plan_trip(self):
        constraints = ['Porto', 'Prague', 'Reykjavik', 'Santorini', 'Amsterdam', 'Munich']
        days = 16
        itinerary = self.generate_itinerary(days, constraints)
        return json.dumps(itinerary, indent=4)

if __name__ == '__main__':
    trip_planner = TripPlanner()
    print(trip_planner.plan_trip())