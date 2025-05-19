import os
from kani import Kani
from kani.engines.huggingface import HuggingEngine
import asyncio
from argparse import ArgumentParser
parser = ArgumentParser()
parser.add_argument("--model", dest="model", help="Model name to use")


model_name = parser.parse_args().model
engine = HuggingEngine(model_id = model_name, use_auth_token=True, model_load_kwargs={"device_map": "auto", "trust_remote_code": True
})
ai = Kani(engine, system_prompt="")


async def run_model():
    message_code = f"You need to schedule a meeting for Harold and Patrick for half an hour between the work hours of 9:00 to 17:00 on Monday. Harold’s calendar is wide open the entire day. Patrick is busy on Monday during 9:00 to 9:30, 10:30 to 12:00, 12:30 to 13:30, 14:00 to 14:30, 15:00 to 16:30; Find a time that works for everyone’s schedule and constraints. Please provide the final answer in the format of {'HH:MM:HH:MM'} for example: {'10:00:11:00'} Make sure to have the curly brackets like {''} around the time range."
    response = await ai.chat_round_str(message_code)

    print(response)


asyncio.run(run_model()) 