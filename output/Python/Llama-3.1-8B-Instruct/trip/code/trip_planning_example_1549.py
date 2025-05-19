import json
from itertools import combinations

class TripPlanner:
    def __init__(self, cities, days, constraints):
        self.cities = cities
        self.days = days
        self.constraints = constraints
        self.direct_flights = {
            'Prague': ['Riga', 'Tallinn'],
            'Tallinn': ['Prague'],
            'Warsaw': ['Naples', 'Stockholm', 'Riga', 'Tallinn', 'Porto'],
            'Porto': ['Lisbon', 'Warsaw', 'Milan'],
            'Naples': ['Warsaw', 'Milan'],
            'Milan': ['Naples', 'Porto', 'Stockholm', 'Santorini'],
            'Lisbon': ['Stockholm', 'Warsaw', 'Naples', 'Prague', 'Riga', 'Porto'],
            'Santorini': ['Milan', 'Naples'],
            'Riga': ['Prague', 'Tallinn', 'Warsaw', 'Stockholm', 'Lisbon'],
            'Stockholm': ['Milan', 'Lisbon', 'Warsaw', 'Tallinn', 'Prague']
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
        self.add_flight(current_place, 'Milan', current_day, current_day)

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
    cities = ['Prague', 'Tallinn', 'Warsaw', 'Porto', 'Naples', 'Milan', 'Lisbon', 'Santorini', 'Riga', 'Stockholm']
    days = 28
    constraints = [
        {'type':'stay', 'place': 'Prague', 'day_range': 'Day 1-5'},
        {'type':'stay', 'place': 'Tallinn', 'day_range': 'Day 6-8'},
        {'type':'meeting', 'place': 'Tallinn', 'day_range': 'Day 18-20'},
        {'type':'stay', 'place': 'Warsaw', 'day_range': 'Day 9-10'},
        {'type':'stay', 'place': 'Porto', 'day_range': 'Day 11-13'},
        {'type':'stay', 'place': 'Naples', 'day_range': 'Day 14-18'},
        {'type':'meeting', 'place': 'Milan', 'day_range': 'Day 24-26'},
        {'type':'stay', 'place': 'Lisbon', 'day_range': 'Day 15-20'},
        {'type':'stay', 'place': 'Santorini', 'day_range': 'Day 21-25'},
        {'type':'stay', 'place': 'Riga', 'day_range': 'Day 10-14'},
        {'type':'meeting', 'place': 'Riga', 'day_range': 'Day 5-8'},
        {'type':'stay', 'place': 'Stockholm', 'day_range': 'Day 20-21'},
        {'type': 'flight', 'to': 'Milan', 'day_range': 'Day 1-1'},
        {'type': 'flight', 'to': 'Prague', 'day_range': 'Day 1-1'}
    ]

    planner = TripPlanner(cities, days, constraints)
    planner.compute_itinerary()
    planner.print_itinerary()


if __name__ == '__main__':
    main()