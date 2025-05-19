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
        self.direct_flights = {
            'Milan': ['Frankfurt', 'Split'],
            'Split': ['Frankfurt', 'Milan', 'Vilnius'],
            'Brussels': ['Vilnius', 'Helsinki', 'Istanbul', 'Milan', 'Frankfurt'],
            'Helsinki': ['Brussels', 'Istanbul', 'Vilnius', 'Dubrovnik', 'Milan', 'Frankfurt'],
            'Istanbul': ['Brussels', 'Helsinki', 'Milan', 'Frankfurt', 'Vilnius'],
            'Vilnius': ['Brussels', 'Helsinki', 'Split', 'Frankfurt'],
            'Frankfurt': ['Milan', 'Split', 'Brussels', 'Vilnius', 'Dubrovnik'],
            'Dubrovnik': ['Istanbul', 'Frankfurt']
        }
        self.itinerary = []
        self.current_day = 1

    def plan_trip(self):
        # Start with Istanbul for the annual show
        self.add_place('Istanbul', 5)
        # Fly to Milan
        self.add_flight('Istanbul', 'Milan')
        self.add_place('Milan', 4)
        # Fly to Split
        self.add_flight('Milan', 'Split')
        self.add_place('Split', 4)
        # Fly to Dubrovnik
        self.add_flight('Split', 'Dubrovnik')
        self.add_place('Dubrovnik', 2)
        # Fly to Frankfurt
        self.add_flight('Dubrovnik', 'Frankfurt')
        self.add_place('Frankfurt', 3)
        # Fly to Vilnius for the workshop
        self.add_flight('Frankfurt', 'Vilnius')
        self.add_place('Vilnius', 5)
        # Fly to Helsinki
        self.add_flight('Vilnius', 'Helsinki')
        self.add_place('Helsinki', 3)
        # Fly to Brussels
        self.add_flight('Helsinki', 'Brussels')
        self.add_place('Brussels', 3)

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