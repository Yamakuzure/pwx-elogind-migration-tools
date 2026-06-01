/**
 * @file Logger.cpp
 * @brief Implementation of the Logger class
 */

#include "Logger.h"

#include <cstdarg>
#include <cstring>
#include <iomanip>
#include <iostream>
#include <sstream>

namespace elomig {

std::string const Logger::LEVEL_NAMES[] = {
	"",        // 0 (unused)
	"debug",   // 1
	"info",    // 2
	"status",  // 3
	"warning", // 4
	"error"    // 5
};

Logger::~Logger() {
	if ( m_logFile.is_open() ) {
		m_logFile.close();
	}
}

Logger& Logger::getInstance() {
	static Logger instance;
	return instance;
}

void Logger::initialize( std::string const& logFile, LogLevel minLevel, bool showDebug ) {
	std::lock_guard< std::mutex > lock( m_mutex );

	if ( m_initialized ) {
		return;
	}

	m_minLevel    = minLevel;
	m_debugMode   = showDebug;
	m_globalError = 0;

	if ( !logFile.empty() ) {
		m_logFilePath = logFile;
		m_logFile.open( logFile, std::ios::app );
		if ( !m_logFile.is_open() ) {
			std::cerr << "Warning: Could not open log file: " << logFile << std::endl;
		}
	}

	m_initialized = true;
}

void Logger::setLogLevel( LogLevel level ) {
	std::lock_guard< std::mutex > lock( m_mutex );
	m_minLevel = level;
}

void Logger::setDebugMode( bool enabled ) {
	std::lock_guard< std::mutex > lock( m_mutex );
	m_debugMode = enabled;
}

void Logger::debug( char const* format, ... ) {
	if ( m_minLevel > LogLevel::DEBUG_LEVEL || !m_debugMode ) {
		return;
	}

	va_list args;
	va_start( args, format );
	log( LogLevel::DEBUG_LEVEL, format, args );
	va_end( args );
}

void Logger::info( char const* format, ... ) {
	if ( m_minLevel > LogLevel::INFO ) {
		return;
	}

	va_list args;
	va_start( args, format );
	log( LogLevel::INFO, format, args );
	va_end( args );
}

void Logger::status( char const* format, ... ) {
	if ( m_minLevel > LogLevel::STATUS ) {
		return;
	}

	va_list args;
	va_start( args, format );
	log( LogLevel::STATUS, format, args );
	va_end( args );
}

void Logger::warning( char const* format, ... ) {
	va_list args;
	va_start( args, format );
	log( LogLevel::WARNING, format, args );
	va_end( args );
}

void Logger::error( char const* format, ... ) {
	va_list args;
	va_start( args, format );
	log( LogLevel::ERROR, format, args );
	va_end( args );

	// Set global error flag
	m_globalError = 1;
}

void Logger::progress( bool isProgress, char const* format, ... ) {
	if ( m_minLevel > LogLevel::STATUS ) {
		return;
	}

	va_list args;
	va_start( args, format );

	char buffer[4'096];
	vsnprintf( buffer, sizeof( buffer ), format, args );
	va_end( args );

	std::string message( buffer );

	if ( isProgress ) {
		// Progress message - use carriage return
		std::cout << "\r" << std::flush;
		std::cout << message << std::flush;
	} else {
		// Regular message
		std::cout << message << std::endl;
	}

	if ( m_logFile.is_open() ) {
		m_logFile << getTimestamp() << " | " << message << std::endl;
	}
}

void Logger::log( LogLevel level, char const* format, va_list args ) {
	if ( level < m_minLevel ) {
		return;
	}

	char buffer[4'096];
	vsnprintf( buffer, sizeof( buffer ), format, args );

	std::string message( buffer );
	output( level, message );
}

void Logger::output( LogLevel level, std::string const& message ) {
	std::lock_guard< std::mutex > lock( m_mutex );

	std::string                   timestamp = getTimestamp();
	std::string                   levelName = LEVEL_NAMES[static_cast< int >( level )];

	// Format: timestamp|-level-| message
	std::string formatted = timestamp + "|-" + levelName + "-| " + message;

	// Output to console
	if ( level >= LogLevel::STATUS || m_debugMode ) {
		if ( level == LogLevel::ERROR ) {
			std::cerr << formatted << std::endl;
		} else {
			std::cout << formatted << std::endl;
		}
	}

	// Output to file
	if ( m_logFile.is_open() ) {
		m_logFile << formatted << std::endl;
	}
}

std::string Logger::getTimestamp() const {
	time_t     now     = time( nullptr );
	struct tm* tm_info = localtime( &now );

	char       buffer[32];
	strftime( buffer, sizeof( buffer ), "%Y-%m-%d %H:%M:%S", tm_info );

	return std::string( buffer );
}

} // namespace elomig
