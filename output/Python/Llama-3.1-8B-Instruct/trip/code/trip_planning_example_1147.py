import json

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Brussels': 3,
            'Helsinki': 3,
            'Split': 4,
            'Dubrovnik': 2,
            'Istanbul': 5,
            'Milan': 4,
            'Vilnius': 5,
            'Frankfurt': 3
        }
        self.flights = {
            ('Milan', 'Frankfurt'): 1,
            ('Split', 'Frankfurt'): 1,
            ('Milan', 'Split'): 1,
            ('Brussels', 'Vilnius'): 1,
            ('Brussels', 'Helsinki'): 1,
            ('Istanbul', 'Brussels'): 1,
            ('Milan', 'Vilnius'): 1,
            ('Brussels', 'Milan'): 1,
            ('Istanbul', 'Helsinki'): 1,
            ('Helsinki', 'Vilnius'): 1,
            ('Helsinki', 'Dubrovnik'): 1,
            ('Split', 'Vilnius'): 1,
            ('Dubrovnik', 'Istanbul'): 1,
            ('Istanbul', 'Milan'): 1,
            ('Helsinki', 'Frankfurt'): 1,
            ('Istanbul', 'Vilnius'): 1,
            ('Split', 'Helsinki'): 1,
            ('Milan', 'Helsinki'): 1,
            ('Istanbul', 'Frankfurt'): 1,
            ('Brussels', 'Frankfurt'): 1,
            ('Dubrovnik', 'Frankfurt'): 1,
            ('Frankfurt', 'Vilnius'): 1
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

        # Add workshop and wedding constraints
        for i, item in enumerate(optimal_itinerary):
            if 'Vilnius' in item['place'] and days_in_city == 5 and 18 <= days_left + days_in_city <= 22:
                optimal_itinerary[i]['day_range'] = f'Day {days_left+1}-{days}'
            if 'Frankfurt' in item['place'] and days_in_city == 3 and 16 <= days_left + days_in_city <= 18:
                optimal_itinerary[i]['day_range'] = f'Day {days_left+1}-{days}'

        # Add annual show constraint
        for i, item in enumerate(optimal_itinerary):
            if 'Istanbul' in item['place'] and days_in_city == 5 and 1 <= days_left + days_in_city <= 5:
                optimal_itinerary[i]['day_range'] = f'Day {days_left+1}-{days}'

        return optimal_itinerary

    def plan_trip(self):
        constraints = ['Brussels', 'Helsinki', 'Split', 'Dubrovnik', 'Istanbul', 'Milan', 'Vilnius', 'Frankfurt']
        days = 22
        itinerary = self.generate_itinerary(days, constraints)
        return json.dumps(itinerary, indent=4)

if __name__ == '__main__':
    trip_planner = TripPlanner()
    print(trip_planner.plan_trip())