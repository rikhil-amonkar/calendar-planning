from datetime import datetime, timedelta

class Person:
    def __init__(self, name):
        self.name = name
        self.busy_slots = []

    def add_busy_slot(self, start_time, end_time):
        self.busy_slots.append((start_time, end_time))

def find_available_time(person1, person2, start_time, end_time, meeting_duration):
    person2_busy_slots = person2.busy_slots

    current_time = start_time
    while current_time < end_time:
        end_current_time = current_time + timedelta(minutes=meeting_duration)

        is_available = True
        for busy_slot in person2_busy_slots:
            if (current_time >= busy_slot[0] and current_time < busy_slot[1]) or \
               (end_current_time > busy_slot[0] and end_current_time <= busy_slot[1]) or \
               (current_time <= busy_slot[0] and end_current_time >= busy_slot[1]):
                is_available = False
                break

        if is_available:
            return current_time, end_current_time

        current_time += timedelta(minutes=30)

    return None

def main():
    person1 = Person("Harold")
    person2 = Person("Patrick")

    start_time = datetime.strptime("09:00", "%H:%M")
    end_time = datetime.strptime("17:00", "%H:%M")

    meeting_duration = 30

    person2.add_busy_slot(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M"))
    person2.add_busy_slot(datetime.strptime("10:30", "%H:%M"), datetime.strptime("12:00", "%H:%M"))
    person2.add_busy_slot(datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:30", "%H:%M"))
    person2.add_busy_slot(datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M"))
    person2.add_busy_slot(datetime.strptime("15:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))

    available_time = find_available_time(person1, person2, start_time, end_time, meeting_duration)

    if available_time:
        print("Here is the proposed time: Monday, {} - {}".format(available_time[0].strftime("%H:%M"), available_time[1].strftime("%H:%M")))
    else:
        print("No available time found.")

if __name__ == "__main__":
    main()
