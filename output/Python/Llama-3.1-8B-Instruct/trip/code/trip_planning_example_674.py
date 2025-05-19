import json

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Helsinki': 2,
            'Warsaw': 3,
            'Madrid': 4,
            'Split': 4,
            'Reykjavik': 2,
            'Budapest': 4
        }
        self.flights = {
            ('Helsinki', 'Reykjavik'): 1,
            ('Budapest', 'Warsaw'): 1,
            ('Madrid', 'Split'): 1,
            ('Helsinki', 'Split'): 1,
            ('Helsinki', 'Madrid'): 1,
            ('Helsinki', 'Budapest'): 1,
            ('Reykjavik', 'Warsaw'): 1,
            ('Helsinki', 'Warsaw'): 1,
            ('Madrid', 'Budapest'): 1,
            ('Budapest', 'Reykjavik'): 1,
            ('Madrid', 'Warsaw'): 1,
            ('Warsaw', 'Split'): 1,
            ('Reykjavik', 'Madrid'): 1
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

        # Add workshop and meeting constraints
        for i, item in enumerate(optimal_itinerary):
            if 'Helsinki' in item['place'] and days_in_city == 2 and 1 <= days_left + days_in_city <= 2:
                optimal_itinerary[i]['day_range'] = f'Day 1-{days}'
            if 'Reykjavik' in item['place'] and days_in_city == 2 and 8 <= days_left + days_in_city <= 9:
                optimal_itinerary[i]['day_range'] = f'Day {days_left+1}-{days}'

        return optimal_itinerary

    def plan_trip(self):
        constraints = ['Helsinki', 'Warsaw', 'Madrid', 'Split', 'Reykjavik', 'Budapest']
        days = 14
        itinerary = self.generate_itinerary(days, constraints)
        return json.dumps(itinerary, indent=4)

if __name__ == '__main__':
    trip_planner = TripPlanner()
    print(trip_planner.plan_trip())