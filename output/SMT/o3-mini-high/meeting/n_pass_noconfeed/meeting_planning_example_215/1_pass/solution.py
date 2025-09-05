from z3 import *
import json

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    # Create an Optimize object
    opt = Optimize()

    # Boolean variables indicating whether to meet each friend.
    doJason = Bool('doJason')
    doJessica = Bool('doJessica')
    doSandra = Bool('doSandra')

    # Integer variables for meeting start and end times (in minutes from midnight).
    start_jason = Int('start_jason')
    end_jason = Int('end_jason')
    start_jessica = Int('start_jessica')
    end_jessica = Int('end_jessica')
    start_sandra = Int('start_sandra')
    end_sandra = Int('end_sandra')

    # ---------------------------
    # Meeting constraints
    # ---------------------------
    # Jason is at Fisherman's Wharf from 16:00 to 16:45 and needs at least 30 minutes.
    opt.add(Implies(doJason, start_jason >= 16 * 60))
    opt.add(Implies(doJason, end_jason <= 16 * 60 + 45))
    opt.add(Implies(doJason, end_jason - start_jason >= 30))
    # Jessica is at Embarcadero from 16:45 to 19:00 and needs at least 30 minutes.
    opt.add(Implies(doJessica, start_jessica >= 16 * 60 + 45))
    opt.add(Implies(doJessica, end_jessica <= 19 * 60))
    opt.add(Implies(doJessica, end_jessica - start_jessica >= 30))
    # Sandra is at Richmond District from 18:30 to 21:45 and needs at least 120 minutes.
    opt.add(Implies(doSandra, start_sandra >= 18 * 60 + 30))
    opt.add(Implies(doSandra, end_sandra <= 21 * 60 + 45))
    opt.add(Implies(doSandra, end_sandra - start_sandra >= 120))

    # ---------------------------
    # Travel constraints between meetings
    # ---------------------------
    # You start at Bayview at 9:00. (9:00 = 9*60 = 540)
    # Bayview -> Fisherman's Wharf takes 25 minutes.
    # (Since Jason's available time [960,1005] is much later than 540+25, no extra constraint is needed here.)
    #
    # If you meet Jason then Jessica (Jason at Fisherman's Wharf and Jessica at Embarcadero):
    # Fisherman's Wharf -> Embarcadero takes 8 minutes.
    opt.add(Implies(And(doJason, doJessica), start_jessica >= end_jason + 8))
    # If you meet Jessica then Sandra (Jessica at Embarcadero and Sandra at Richmond District):
    # Embarcadero -> Richmond District takes 21 minutes.
    opt.add(Implies(And(doJessica, doSandra), start_sandra >= end_jessica + 21))
    # Alternatively, if you meet Jason and Sandra but skip Jessica:
    # Fisherman's Wharf -> Richmond District takes 18 minutes.
    opt.add(Implies(And(doJason, Not(doJessica), doSandra), start_sandra >= end_jason + 18))

    # Optional: If a meeting is the first one (other than Jason) then account for travel directly from Bayview.
    # Bayview -> Embarcadero = 19 minutes.
    opt.add(Implies(And(Not(doJason), doJessica), start_jessica >= 540 + 19))
    # Bayview -> Richmond District = 25 minutes.
    opt.add(Implies(And(Not(doJason), Not(doJessica), doSandra), start_sandra >= 540 + 25))

    # ---------------------------
    # Optimization Objective
    # ---------------------------
    # Primary goal: maximize the number of meetings.
    meet_count = If(doJason, 1, 0) + If(doJessica, 1, 0) + If(doSandra, 1, 0)
    opt.maximize(meet_count)
    # Secondary goal: if meeting Sandra, finish as early as possible.
    opt.minimize(If(doSandra, end_sandra, 10000))

    # ---------------------------
    # Check and extract a model
    # ---------------------------
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        # For each meeting that is scheduled, collect the details.
        if is_true(model.evaluate(doJason)):
            st = model.evaluate(start_jason).as_long()
            et = model.evaluate(end_jason).as_long()
            itinerary.append({
                "action": "meet",
                "location": "Fisherman's Wharf",
                "person": "Jason",
                "start_time": minutes_to_time(st),
                "end_time": minutes_to_time(et)
            })
        if is_true(model.evaluate(doJessica)):
            st = model.evaluate(start_jessica).as_long()
            et = model.evaluate(end_jessica).as_long()
            itinerary.append({
                "action": "meet",
                "location": "Embarcadero",
                "person": "Jessica",
                "start_time": minutes_to_time(st),
                "end_time": minutes_to_time(et)
            })
        if is_true(model.evaluate(doSandra)):
            st = model.evaluate(start_sandra).as_long()
            et = model.evaluate(end_sandra).as_long()
            itinerary.append({
                "action": "meet",
                "location": "Richmond District",
                "person": "Sandra",
                "start_time": minutes_to_time(st),
                "end_time": minutes_to_time(et)
            })
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        # If no meeting plan is found, output an empty itinerary.
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()