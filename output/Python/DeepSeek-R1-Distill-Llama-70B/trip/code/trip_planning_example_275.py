import json

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Vilnius': 4,
            'Split': 5,
            'Madrid': 6,
            'Santorini': 2
        }
        self.direct_flights = {
            'Vilnius': ['Split'],
            'Split': ['Madrid'],
            'Madrid': ['Santorini'],
            'Santorini': []
        }
        self.itinerary = []
        self.current_day = 1

    def plan_trip(self):
        # Start with Vilnius
        self.add_place('Vilnius', 4)
        # Fly to Split
        self.add_flight('Vilnius', 'Split')
        self.add_place('Split', 5)
        # Fly to Madrid
        self.add_flight('Split', 'Madrid')
        self.add_place('Madrid', 6)
        # Fly to Santorini for the conference
        self.add_flight('Madrid', 'Santorini')
        self.add_place('Santorini', 2)

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