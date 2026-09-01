"""Application entry point.
  - app.web: FastAPI application
  - app.update: device update engine
  - app.discord_bot: discord bot/notifications
"""

from app.web import app


if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=8000)
