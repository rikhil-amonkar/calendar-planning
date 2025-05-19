import json
from itertools import combinations

class TripPlanner:
    def __init__(self, cities, days, constraints):
        self.cities = cities
        self.days = days
        self.constraints = constraints
        self.direct_flights = {
            'Helsinki': ['Reykjavik', 'Vilnius'],
            'Reykjavik': [],
            'Vilnius': ['Helsinki'],
            'Split': ['Geneva', 'Vilnius'],
            'Geneva': ['Split', 'Helsinki']
        }
        self.itinerary = []

    def compute_itinerary(self):
        # Sort constraints by day range
        sorted_constraints = sorted(self.constraints, key=lambda x: x['day_range'])

        # Initialize current place and day
        current_place = sorted_constraints[0]['place']
        current_day = 1

        # Iterate over constraints
        for constraint in sorted_constraints:
            # If constraint is a stay, move to the next day
            if constraint['type'] =='stay':
                stay_days = int(constraint['day_range'].split('-')[1]) - current_day + 1
                # Add stay to the itinerary
                self.add_stay(current_place, current_day, current_day + stay_days - 1)
                current_day += stay_days
            # If constraint is a flight, move to the next day
            elif constraint['type'] == 'flight':
                flight_days = 1
                # Add flight to the itinerary
                self.add_flight(current_place, constraint['to'], current_day, current_day)
                current_place = constraint['to']
                current_day += flight_days

        # Add last flight to the itinerary
        self.add_flight(current_place, 'Geneva', current_day, current_day)

    def add_flight(self, from_place, to_place, day, last_day):
        self.itinerary.append({
            'day_range': f'Day {day}-{last_day}',
            'flying': f'Day {day}-{day}',
            'from': from_place,
            'to': to_place
        })

    def add_stay(self, place, start_day, end_day):
        self.itinerary.append({
            'day_range': f'Day {start_day}-{end_day}',
            'place': place
        })

    def print_itinerary(self):
        print(json.dumps(self.itinerary, indent=4))


def main():
    cities = ['Split', 'Helsinki', 'Reykjavik', 'Vilnius', 'Geneva']
    days = 12
    constraints = [
        {'type':'stay', 'place': 'Split', 'day_range': 'Day 1-2'},
        {'type':'stay', 'place': 'Helsinki', 'day_range': 'Day 2-4'},
        {'type':'stay', 'place': 'Reykjavik', 'day_range': 'Day 4-7'},
        {'type':'meeting', 'place': 'Reykjavik', 'day_range': 'Day 10-12'},
        {'type':'stay', 'place': 'Vilnius', 'day_range': 'Day 7-9'},
        {'type':'meeting', 'place': 'Vilnius', 'day_range': 'Day 7-9'},
        {'type':'stay', 'place': 'Geneva', 'day_range': 'Day 4-10'},
        {'type': 'flight', 'to': 'Geneva', 'day_range': 'Day 1-1'},
        {'type': 'flight', 'to': 'Split', 'day_range': 'Day 1-1'},
        {'type': 'flight', 'to': 'Helsinki', 'day_range': 'Day 1-1'}
    ]

    planner = TripPlanner(cities, days, constraints)
    planner.compute_itinerary()
    planner.print_itinerary()


if __name__ == '__main__':
    main()