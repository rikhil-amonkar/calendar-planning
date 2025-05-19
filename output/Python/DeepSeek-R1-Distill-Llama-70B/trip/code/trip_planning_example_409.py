import json

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Zurich': 3,
            'Hamburg': 2,
            'Helsinki': 2,
            'Bucharest': 2,
            'Split': 7
        }
        self.direct_flights = {
            'Zurich': ['Helsinki', 'Hamburg', 'Bucharest', 'Split'],
            'Helsinki': ['Zurich', 'Hamburg', 'Split'],
            'Hamburg': ['Zurich', 'Helsinki', 'Bucharest', 'Split'],
            'Bucharest': ['Zurich', 'Hamburg', 'Split'],
            'Split': ['Zurich', 'Helsinki', 'Hamburg', 'Bucharest']
        }
        self.itinerary = []
        self.current_day = 1

    def plan_trip(self):
        # Start with Zurich for the wedding
        self.add_place('Zurich', 3)
        # Next, go to Split for the conference
        self.add_flight('Zurich', 'Split')
        self.add_place('Split', 7)
        # Then visit Helsinki
        self.add_flight('Split', 'Helsinki')
        self.add_place('Helsinki', 2)
        # Next, go to Hamburg
        self.add_flight('Helsinki', 'Hamburg')
        self.add_place('Hamburg', 2)
        # Finally, visit Bucharest
        self.add_flight('Hamburg', 'Bucharest')
        self.add_place('Bucharest', 2)

    def add_place(self, place, days):
        end_day = self.current_day + days - 1
        self.itinerary.append({'day_range': f'Day {self.current_day}-{end_day}', 'place': place})
        self.current_day = end_day + 1

    def add_flight(self, from_city, to_city):
        self.itinerary.append({'flying': f'Day {self.current_day}-{self.current_day}', 'from': from_city, 'to': to_city})
        self.current_day += 1

planner = TripPlanner()
planner.plan_trip()
print(json.dumps(planner.itinerary))