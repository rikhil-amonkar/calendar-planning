import json

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Reykjavik': 2,
            'Stockholm': 2,
            'Porto': 5,
            'Nice': 3,
            'Venice': 4,
            'Vienna': 3,
            'Split': 3,
            'Copenhagen': 2
        }
        self.direct_flights = {
            'Copenhagen': ['Vienna', 'Nice', 'Stockholm', 'Reykjavik', 'Porto', 'Venice'],
            'Nice': ['Stockholm', 'Reykjavik', 'Porto', 'Venice', 'Vienna', 'Copenhagen'],
            'Split': ['Copenhagen', 'Vienna'],
            'Reykjavik': ['Vienna', 'Copenhagen', 'Stockholm', 'Nice'],
            'Stockholm': ['Copenhagen', 'Nice', 'Reykjavik', 'Split'],
            'Porto': ['Vienna', 'Copenhagen'],
            'Venice': ['Vienna', 'Copenhagen'],
            'Vienna': ['Copenhagen', 'Porto', 'Nice', 'Reykjavik', 'Stockholm', 'Split']
        }
        self.itinerary = []
        self.current_day = 1

    def plan_trip(self):
        # Start with Reykjavik
        self.add_place('Reykjavik', 2)
        # Fly to Stockholm
        self.add_flight('Reykjavik', 'Stockholm')
        self.add_place('Stockholm', 2)
        # Fly to Copenhagen
        self.add_flight('Stockholm', 'Copenhagen')
        self.add_place('Copenhagen', 2)
        # Fly to Nice
        self.add_flight('Copenhagen', 'Nice')
        self.add_place('Nice', 3)
        # Fly to Venice
        self.add_flight('Nice', 'Venice')
        self.add_place('Venice', 4)
        # Fly to Vienna
        self.add_flight('Venice', 'Vienna')
        self.add_place('Vienna', 3)
        # Fly to Split
        self.add_flight('Vienna', 'Split')
        self.add_place('Split', 3)
        # Fly to Porto
        self.add_flight('Split', 'Porto')
        self.add_place('Porto', 5)

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