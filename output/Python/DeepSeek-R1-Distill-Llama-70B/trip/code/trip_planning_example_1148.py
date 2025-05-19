import json

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Lisbon': 2,
            'Dubrovnik': 5,
            'Copenhagen': 5,
            'Prague': 3,
            'Tallinn': 2,
            'Stockholm': 4,
            'Split': 3,
            'Lyon': 2
        }
        self.direct_flights = {
            'Dubrovnik': ['Stockholm'],
            'Lisbon': ['Copenhagen', 'Lyon'],
            'Copenhagen': ['Stockholm', 'Split'],
            'Prague': ['Stockholm', 'Lyon', 'Lisbon', 'Copenhagen'],
            'Tallinn': ['Stockholm', 'Copenhagen', 'Prague'],
            'Stockholm': ['Split', 'Dubrovnik'],
            'Split': ['Lyon'],
            'Lyon': []
        }
        self.itinerary = []
        self.current_day = 1

    def plan_trip(self):
        # Start with Tallinn
        self.add_place('Tallinn', 2)
        # Fly to Prague
        self.add_flight('Tallinn', 'Prague')
        self.add_place('Prague', 3)
        # Fly to Lisbon
        self.add_flight('Prague', 'Lisbon')
        self.add_place('Lisbon', 2)
        # Fly to Dubrovnik
        self.add_flight('Lisbon', 'Dubrovnik')
        self.add_place('Dubrovnik', 5)
        # Fly to Copenhagen
        self.add_flight('Dubrovnik', 'Copenhagen')
        self.add_place('Copenhagen', 5)
        # Fly to Stockholm
        self.add_flight('Copenhagen', 'Stockholm')
        self.add_place('Stockholm', 4)
        # Fly to Split
        self.add_flight('Stockholm', 'Split')
        self.add_place('Split', 3)
        # Fly to Lyon
        self.add_flight('Split', 'Lyon')
        self.add_place('Lyon', 2)

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